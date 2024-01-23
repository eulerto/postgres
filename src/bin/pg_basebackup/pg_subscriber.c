/*-------------------------------------------------------------------------
 *
 * pg_subscriber.c
 *	  Create a new logical replica from a standby server
 *
 * Copyright (C) 2024, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *		src/bin/pg_basebackup/pg_subscriber.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres_fe.h"

#include <signal.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>

#include "access/xlogdefs.h"
#include "catalog/pg_control.h"
#include "common/connect.h"
#include "common/controldata_utils.h"
#include "common/file_perm.h"
#include "common/file_utils.h"
#include "common/logging.h"
#include "fe_utils/recovery_gen.h"
#include "fe_utils/simple_list.h"
#include "getopt_long.h"
#include "utils/pidfile.h"

#define	PGS_OUTPUT_DIR	"pg_subscriber_output.d"

typedef struct LogicalRepInfo
{
	Oid			oid;			/* database OID */
	char	   *dbname;			/* database name */
	char	   *pubconninfo;	/* publication connection string for logical
								 * replication */
	char	   *subconninfo;	/* subscription connection string for logical
								 * replication */
	char	   *pubname;		/* publication name */
	char	   *subname;		/* subscription name (also replication slot
								 * name) */

	bool		made_replslot;	/* replication slot was created */
	bool		made_publication;	/* publication was created */
	bool		made_subscription;	/* subscription was created */
} LogicalRepInfo;

static void cleanup_objects_atexit(void);
static void usage();
static char *get_base_conninfo(char *conninfo, char *dbname,
							   const char *noderole);
static bool get_exec_path(const char *path);
static bool check_data_directory(const char *datadir);
static char *concat_conninfo_dbname(const char *conninfo, const char *dbname);
static LogicalRepInfo *store_pub_sub_info(const char *pub_base_conninfo, const char *sub_base_conninfo);
static PGconn *connect_database(const char *conninfo);
static void disconnect_database(PGconn *conn);
static uint64 get_sysid_from_conn(const char *conninfo);
static uint64 get_control_from_datadir(const char *datadir);
static void modify_sysid(const char *pg_resetwal_path, const char *datadir);
static char *use_primary_slot_name(void);
static bool create_all_logical_replication_slots(LogicalRepInfo *dbinfo);
static char *create_logical_replication_slot(PGconn *conn, LogicalRepInfo *dbinfo,
											 char *slot_name);
static void drop_replication_slot(PGconn *conn, LogicalRepInfo *dbinfo, const char *slot_name);
static void pg_ctl_status(const char *pg_ctl_cmd, int rc, int action);
static void wait_for_end_recovery(const char *conninfo);
static void create_publication(PGconn *conn, LogicalRepInfo *dbinfo);
static void drop_publication(PGconn *conn, LogicalRepInfo *dbinfo);
static void create_subscription(PGconn *conn, LogicalRepInfo *dbinfo);
static void drop_subscription(PGconn *conn, LogicalRepInfo *dbinfo);
static void set_replication_progress(PGconn *conn, LogicalRepInfo *dbinfo, const char *lsn);
static void enable_subscription(PGconn *conn, LogicalRepInfo *dbinfo);

#define	USEC_PER_SEC	1000000
#define	WAIT_INTERVAL	1		/* 1 second */

/* Options */
static const char *progname;

static char *subscriber_dir = NULL;
static char *pub_conninfo_str = NULL;
static char *sub_conninfo_str = NULL;
static SimpleStringList database_names = {NULL, NULL};
static char *primary_slot_name = NULL;
static bool dry_run = false;

static bool success = false;

static char *pg_ctl_path = NULL;
static char *pg_resetwal_path = NULL;

static LogicalRepInfo *dbinfo;
static int	num_dbs = 0;

static char temp_replslot[NAMEDATALEN] = {0};
static bool made_transient_replslot = false;

enum WaitPMResult
{
	POSTMASTER_READY,
	POSTMASTER_STANDBY,
	POSTMASTER_STILL_STARTING,
	POSTMASTER_FAILED
};


/*
 * Cleanup objects that were created by pg_subscriber if there is an error.
 *
 * Replication slots, publications and subscriptions are created. Depending on
 * the step it failed, it should remove the already created objects if it is
 * possible (sometimes it won't work due to a connection issue).
 */
static void
cleanup_objects_atexit(void)
{
	PGconn	   *conn;
	int			i;

	if (success)
		return;

	for (i = 0; i < num_dbs; i++)
	{
		if (dbinfo[i].made_subscription)
		{
			conn = connect_database(dbinfo[i].subconninfo);
			if (conn != NULL)
			{
				drop_subscription(conn, &dbinfo[i]);
				disconnect_database(conn);
			}
		}

		if (dbinfo[i].made_publication || dbinfo[i].made_replslot)
		{
			conn = connect_database(dbinfo[i].pubconninfo);
			if (conn != NULL)
			{
				if (dbinfo[i].made_publication)
					drop_publication(conn, &dbinfo[i]);
				if (dbinfo[i].made_replslot)
					drop_replication_slot(conn, &dbinfo[i], NULL);
				disconnect_database(conn);
			}
		}
	}

	if (made_transient_replslot)
	{
		conn = connect_database(dbinfo[0].pubconninfo);
		if (conn != NULL)
		{
			drop_replication_slot(conn, &dbinfo[0], temp_replslot);
			disconnect_database(conn);
		}
	}
}

static void
usage(void)
{
	printf(_("%s creates a new logical replica from a standby server.\n\n"),
		   progname);
	printf(_("Usage:\n"));
	printf(_("  %s [OPTION]...\n"), progname);
	printf(_("\nOptions:\n"));
	printf(_(" -D, --pgdata=DATADIR                location for the subscriber data directory\n"));
	printf(_(" -P, --publisher-conninfo=CONNINFO   publisher connection string\n"));
	printf(_(" -S, --subscriber-conninfo=CONNINFO  subscriber connection string\n"));
	printf(_(" -d, --database=DBNAME               database to create a subscription\n"));
	printf(_(" -n, --dry-run                       stop before modifying anything\n"));
	printf(_(" -v, --verbose                       output verbose messages\n"));
	printf(_(" -V, --version                       output version information, then exit\n"));
	printf(_(" -?, --help                          show this help, then exit\n"));
	printf(_("\nReport bugs to <%s>.\n"), PACKAGE_BUGREPORT);
	printf(_("%s home page: <%s>\n"), PACKAGE_NAME, PACKAGE_URL);
}

/*
 * Validate a connection string. Returns a base connection string that is a
 * connection string without a database name plus a fallback application name.
 * Since we might process multiple databases, each database name will be
 * appended to this base connection string to provide a final connection string.
 * If the second argument (dbname) is not null, returns dbname if the provided
 * connection string contains it. If option --database is not provided, uses
 * dbname as the only database to setup the logical replica.
 * It is the caller's responsibility to free the returned connection string and
 * dbname.
 */
static char *
get_base_conninfo(char *conninfo, char *dbname, const char *noderole)
{
	PQExpBuffer buf = createPQExpBuffer();
	PQconninfoOption *conn_opts = NULL;
	PQconninfoOption *conn_opt;
	char	   *errmsg = NULL;
	char	   *ret;
	int			i;

	pg_log_info("validating connection string on %s", noderole);

	conn_opts = PQconninfoParse(conninfo, &errmsg);
	if (conn_opts == NULL)
	{
		pg_log_error("could not parse connection string: %s", errmsg);
		return NULL;
	}

	i = 0;
	for (conn_opt = conn_opts; conn_opt->keyword != NULL; conn_opt++)
	{
		if (strcmp(conn_opt->keyword, "dbname") == 0 && conn_opt->val != NULL)
		{
			if (dbname)
				dbname = pg_strdup(conn_opt->val);
			continue;
		}

		if (conn_opt->val != NULL && conn_opt->val[0] != '\0')
		{
			if (i > 0)
				appendPQExpBufferChar(buf, ' ');
			appendPQExpBuffer(buf, "%s=%s", conn_opt->keyword, conn_opt->val);
			i++;
		}
	}

	if (i > 0)
		appendPQExpBufferChar(buf, ' ');
	appendPQExpBuffer(buf, "fallback_application_name=%s", progname);

	ret = pg_strdup(buf->data);

	destroyPQExpBuffer(buf);
	PQconninfoFree(conn_opts);

	return ret;
}

/*
 * Get the absolute path from other PostgreSQL binaries (pg_ctl and
 * pg_resetwal) that is used by it.
 */
static bool
get_exec_path(const char *path)
{
	int			rc;

	pg_ctl_path = pg_malloc(MAXPGPATH);
	rc = find_other_exec(path, "pg_ctl",
						 "pg_ctl (PostgreSQL) " PG_VERSION "\n",
						 pg_ctl_path);
	if (rc < 0)
	{
		char		full_path[MAXPGPATH];

		if (find_my_exec(path, full_path) < 0)
			strlcpy(full_path, progname, sizeof(full_path));
		if (rc == -1)
			pg_log_error("The program \"%s\" is needed by %s but was not found in the\n"
						 "same directory as \"%s\".\n"
						 "Check your installation.",
						 "pg_ctl", progname, full_path);
		else
			pg_log_error("The program \"%s\" was found by \"%s\"\n"
						 "but was not the same version as %s.\n"
						 "Check your installation.",
						 "pg_ctl", full_path, progname);
		return false;
	}

	pg_log_debug("pg_ctl path is: %s", pg_ctl_path);

	pg_resetwal_path = pg_malloc(MAXPGPATH);
	rc = find_other_exec(path, "pg_resetwal",
						 "pg_resetwal (PostgreSQL) " PG_VERSION "\n",
						 pg_resetwal_path);
	if (rc < 0)
	{
		char		full_path[MAXPGPATH];

		if (find_my_exec(path, full_path) < 0)
			strlcpy(full_path, progname, sizeof(full_path));
		if (rc == -1)
			pg_log_error("The program \"%s\" is needed by %s but was not found in the\n"
						 "same directory as \"%s\".\n"
						 "Check your installation.",
						 "pg_resetwal", progname, full_path);
		else
			pg_log_error("The program \"%s\" was found by \"%s\"\n"
						 "but was not the same version as %s.\n"
						 "Check your installation.",
						 "pg_resetwal", full_path, progname);
		return false;
	}

	pg_log_debug("pg_resetwal path is: %s", pg_resetwal_path);

	return true;
}

/*
 * Is it a cluster directory? These are preliminary checks. It is far from
 * making an accurate check. If it is not a clone from the publisher, it will
 * eventually fail in a future step.
 */
static bool
check_data_directory(const char *datadir)
{
	struct stat statbuf;
	char		versionfile[MAXPGPATH];

	pg_log_info("checking if directory \"%s\" is a cluster data directory",
				datadir);

	if (stat(datadir, &statbuf) != 0)
	{
		if (errno == ENOENT)
			pg_log_error("data directory \"%s\" does not exist", datadir);
		else
			pg_log_error("could not access directory \"%s\": %s", datadir, strerror(errno));

		return false;
	}

	snprintf(versionfile, MAXPGPATH, "%s/PG_VERSION", datadir);
	if (stat(versionfile, &statbuf) != 0 && errno == ENOENT)
	{
		pg_log_error("directory \"%s\" is not a database cluster directory", datadir);
		return false;
	}

	return true;
}

/*
 * Append database name into a base connection string.
 *
 * dbname is the only parameter that changes so it is not included in the base
 * connection string. This function concatenates dbname to build a "real"
 * connection string.
 */
static char *
concat_conninfo_dbname(const char *conninfo, const char *dbname)
{
	PQExpBuffer buf = createPQExpBuffer();
	char	   *ret;

	Assert(conninfo != NULL);

	appendPQExpBufferStr(buf, conninfo);
	appendPQExpBuffer(buf, " dbname=%s", dbname);

	ret = pg_strdup(buf->data);
	destroyPQExpBuffer(buf);

	return ret;
}

/*
 * Store publication and subscription information.
 */
static LogicalRepInfo *
store_pub_sub_info(const char *pub_base_conninfo, const char *sub_base_conninfo)
{
	LogicalRepInfo *dbinfo;
	SimpleStringListCell *cell;
	int			i = 0;

	dbinfo = (LogicalRepInfo *) pg_malloc(num_dbs * sizeof(LogicalRepInfo));

	for (cell = database_names.head; cell; cell = cell->next)
	{
		char	   *conninfo;

		/* Publisher. */
		conninfo = concat_conninfo_dbname(pub_base_conninfo, cell->val);
		dbinfo[i].pubconninfo = conninfo;
		dbinfo[i].dbname = cell->val;
		dbinfo[i].made_replslot = false;
		dbinfo[i].made_publication = false;
		dbinfo[i].made_subscription = false;
		/* other struct fields will be filled later. */

		/* Subscriber. */
		conninfo = concat_conninfo_dbname(sub_base_conninfo, cell->val);
		dbinfo[i].subconninfo = conninfo;

		i++;
	}

	return dbinfo;
}

static PGconn *
connect_database(const char *conninfo)
{
	PGconn	   *conn;
	PGresult   *res;
	const char *rconninfo;

	/* logical replication mode */
	rconninfo = psprintf("%s replication=database", conninfo);

	conn = PQconnectdb(rconninfo);
	if (PQstatus(conn) != CONNECTION_OK)
	{
		pg_log_error("connection to database failed: %s", PQerrorMessage(conn));
		return NULL;
	}

	/* secure search_path */
	res = PQexec(conn, ALWAYS_SECURE_SEARCH_PATH_SQL);
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not clear search_path: %s", PQresultErrorMessage(res));
		return NULL;
	}
	PQclear(res);

	return conn;
}

static void
disconnect_database(PGconn *conn)
{
	Assert(conn != NULL);

	PQfinish(conn);
}

/*
 * Obtain the system identifier using the provided connection. It will be used
 * to compare if a data directory is a clone of another one.
 */
static uint64
get_sysid_from_conn(const char *conninfo)
{
	PGconn	   *conn;
	PGresult   *res;
	uint64		sysid;

	pg_log_info("getting system identifier from publisher");

	conn = connect_database(conninfo);
	if (conn == NULL)
		exit(1);

	res = PQexec(conn, "IDENTIFY_SYSTEM");
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not send replication command \"%s\": %s",
					 "IDENTIFY_SYSTEM", PQresultErrorMessage(res));
		PQclear(res);
		disconnect_database(conn);
		exit(1);
	}
	if (PQntuples(res) != 1 || PQnfields(res) < 3)
	{
		pg_log_error("could not identify system: got %d rows and %d fields, expected %d rows and %d or more fields",
					 PQntuples(res), PQnfields(res), 1, 3);

		PQclear(res);
		disconnect_database(conn);
		exit(1);
	}

	sysid = strtou64(PQgetvalue(res, 0, 0), NULL, 10);

	pg_log_info("system identifier is %llu on publisher", (unsigned long long) sysid);

	disconnect_database(conn);

	return sysid;
}

/*
 * Obtain the system identifier from control file. It will be used to compare
 * if a data directory is a clone of another one. This routine is used locally
 * and avoids a replication connection.
 */
static uint64
get_control_from_datadir(const char *datadir)
{
	ControlFileData *cf;
	bool		crc_ok;
	uint64		sysid;

	pg_log_info("getting system identifier from subscriber");

	cf = get_controlfile(datadir, &crc_ok);
	if (!crc_ok)
	{
		pg_log_error("control file appears to be corrupt");
		exit(1);
	}

	sysid = cf->system_identifier;

	pg_log_info("system identifier is %llu on subscriber", (unsigned long long) sysid);

	pfree(cf);

	return sysid;
}

/*
 * Modify the system identifier. Since a standby server preserves the system
 * identifier, it makes sense to change it to avoid situations in which WAL
 * files from one of the systems might be used in the other one.
 */
static void
modify_sysid(const char *pg_resetwal_path, const char *datadir)
{
	ControlFileData *cf;
	bool		crc_ok;
	struct timeval tv;

	char	   *cmd_str;
	int			rc;

	pg_log_info("modifying system identifier from subscriber");

	cf = get_controlfile(datadir, &crc_ok);
	if (!crc_ok)
	{
		pg_log_error("control file appears to be corrupt");
		exit(1);
	}

	/*
	 * Select a new system identifier.
	 *
	 * XXX this code was extracted from BootStrapXLOG().
	 */
	gettimeofday(&tv, NULL);
	cf->system_identifier = ((uint64) tv.tv_sec) << 32;
	cf->system_identifier |= ((uint64) tv.tv_usec) << 12;
	cf->system_identifier |= getpid() & 0xFFF;

	if (!dry_run)
		update_controlfile(datadir, cf, true);

	pg_log_info("system identifier is %llu on subscriber", (unsigned long long) cf->system_identifier);

	pg_log_info("running pg_resetwal on the subscriber");

	cmd_str = psprintf("\"%s\" -D \"%s\"", pg_resetwal_path, datadir);

	pg_log_debug("command is: %s", cmd_str);

	if (!dry_run)
	{
		rc = system(cmd_str);
		if (rc == 0)
			pg_log_info("subscriber successfully changed the system identifier");
		else
			pg_log_error("subscriber failed to change system identifier: exit code: %d", rc);
	}

	pfree(cf);
}

/*
 * Return a palloc'd slot name if the replication is using one.
 */
static char *
use_primary_slot_name(void)
{
	PGconn	   *conn;
	PGresult   *res;
	PQExpBuffer str = createPQExpBuffer();
	char	   *slot_name;

	conn = connect_database(dbinfo[0].subconninfo);
	if (conn == NULL)
		exit(1);

	res = PQexec(conn, "SELECT setting FROM pg_settings WHERE name = 'primary_slot_name'");
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain parameter information: %s", PQresultErrorMessage(res));
		return NULL;
	}

	/*
	 * If primary_slot_name is an empty string, the current replication
	 * connection is not using a replication slot, bail out.
	 */
	if (strcmp(PQgetvalue(res, 0, 0), "") == 0)
	{
		PQclear(res);
		return NULL;
	}

	slot_name = pg_strdup(PQgetvalue(res, 0, 0));
	PQclear(res);

	disconnect_database(conn);

	conn = connect_database(dbinfo[0].pubconninfo);
	if (conn == NULL)
		exit(1);

	appendPQExpBuffer(str,
					  "SELECT 1 FROM pg_replication_slots r INNER JOIN pg_stat_activity a ON (r.active_pid = a.pid) WHERE slot_name = '%s'", slot_name);

	pg_log_debug("command is: %s", str->data);

	res = PQexec(conn, str->data);
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain replication slot information: %s", PQresultErrorMessage(res));
		return NULL;
	}

	if (PQntuples(res) != 1)
	{
		pg_log_error("could not obtain replication slot information: got %d rows, expected %d row",
					 PQntuples(res), 1);
		return NULL;
	}

	PQclear(res);
	disconnect_database(conn);

	return slot_name;
}

static bool
create_all_logical_replication_slots(LogicalRepInfo *dbinfo)
{
	int			i;

	for (i = 0; i < num_dbs; i++)
	{
		PGconn	   *conn;
		PGresult   *res;
		char		replslotname[NAMEDATALEN];

		conn = connect_database(dbinfo[i].pubconninfo);
		if (conn == NULL)
			exit(1);

		res = PQexec(conn,
					 "SELECT oid FROM pg_catalog.pg_database WHERE datname = current_database()");
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not obtain database OID: %s", PQresultErrorMessage(res));
			return false;
		}

		if (PQntuples(res) != 1)
		{
			pg_log_error("could not obtain database OID: got %d rows, expected %d rows",
						 PQntuples(res), 1);
			return false;
		}

		/* Remember database OID. */
		dbinfo[i].oid = strtoul(PQgetvalue(res, 0, 0), NULL, 10);

		PQclear(res);

		/*
		 * Build the replication slot name. The name must not exceed
		 * NAMEDATALEN - 1. This current schema uses a maximum of 36
		 * characters (14 + 10 + 1 + 10 + '\0'). System identifier is included
		 * to reduce the probability of collision. By default, subscription
		 * name is used as replication slot name.
		 */
		snprintf(replslotname, sizeof(replslotname),
				 "pg_subscriber_%u_%d",
				 dbinfo[i].oid,
				 (int) getpid());
		dbinfo[i].subname = pg_strdup(replslotname);

		/* Create replication slot on publisher. */
		if (create_logical_replication_slot(conn, &dbinfo[i], replslotname) != NULL || dry_run)
			pg_log_info("create replication slot \"%s\" on publisher", replslotname);
		else
			return false;

		disconnect_database(conn);
	}

	return true;
}

/*
 * Create a logical replication slot and returns a consistent LSN. The returned
 * LSN might be used to catch up the subscriber up to the required point.
 *
 * CreateReplicationSlot() is not used because it does not provide the one-row
 * result set that contains the consistent LSN.
 */
static char *
create_logical_replication_slot(PGconn *conn, LogicalRepInfo *dbinfo,
								char *slot_name)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res = NULL;
	char	   *lsn = NULL;
	bool		transient_replslot = false;

	Assert(conn != NULL);

	/*
	 * If no slot name is informed, it is a transient replication slot used
	 * only for catch up purposes.
	 */
	if (slot_name[0] == '\0')
	{
		snprintf(slot_name, NAMEDATALEN, "pg_subscriber_%d_startpoint",
				 (int) getpid());
		transient_replslot = true;
	}

	pg_log_info("creating the replication slot \"%s\" on database \"%s\"", slot_name, dbinfo->dbname);

	appendPQExpBuffer(str, "CREATE_REPLICATION_SLOT \"%s\"", slot_name);
	appendPQExpBufferStr(str, " LOGICAL \"pgoutput\" NOEXPORT_SNAPSHOT");

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not create replication slot \"%s\" on database \"%s\": %s", slot_name, dbinfo->dbname,
						 PQresultErrorMessage(res));
			return lsn;
		}
	}

	/* for cleanup purposes */
	if (transient_replslot)
		made_transient_replslot = true;
	else
		dbinfo->made_replslot = true;

	if (!dry_run)
	{
		lsn = pg_strdup(PQgetvalue(res, 0, 1));
		PQclear(res);
	}

	destroyPQExpBuffer(str);

	return lsn;
}

static void
drop_replication_slot(PGconn *conn, LogicalRepInfo *dbinfo, const char *slot_name)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("dropping the replication slot \"%s\" on database \"%s\"", slot_name, dbinfo->dbname);

	appendPQExpBuffer(str, "DROP_REPLICATION_SLOT \"%s\"", slot_name);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
			pg_log_error("could not drop replication slot \"%s\" on database \"%s\": %s", slot_name, dbinfo->dbname,
						 PQerrorMessage(conn));

		PQclear(res);
	}

	destroyPQExpBuffer(str);
}

/*
 * Reports a suitable message if pg_ctl fails.
 */
static void
pg_ctl_status(const char *pg_ctl_cmd, int rc, int action)
{
	if (rc != 0)
	{
		if (WIFEXITED(rc))
		{
			pg_log_error("pg_ctl failed with exit code %d", WEXITSTATUS(rc));
		}
		else if (WIFSIGNALED(rc))
		{
#if defined(WIN32)
			pg_log_error("pg_ctl was terminated by exception 0x%X", WTERMSIG(rc));
			pg_log_error_detail("See C include file \"ntstatus.h\" for a description of the hexadecimal value.");
#else
			pg_log_error("pg_ctl was terminated by signal %d: %s",
						 WTERMSIG(rc), pg_strsignal(WTERMSIG(rc)));
#endif
		}
		else
		{
			pg_log_error("pg_ctl exited with unrecognized status %d", rc);
		}

		pg_log_error_detail("The failed command was: %s", pg_ctl_cmd);
		exit(1);
	}

	if (action)
		pg_log_info("postmaster was started");
	else
		pg_log_info("postmaster was stopped");
}

/*
 * Returns after the server finishes the recovery process.
 */
static void
wait_for_end_recovery(const char *conninfo)
{
	PGconn	   *conn;
	PGresult   *res;
	int			status = POSTMASTER_STILL_STARTING;

	pg_log_info("waiting the postmaster to reach the consistent state");

	conn = connect_database(conninfo);
	if (conn == NULL)
		exit(1);

	for (;;)
	{
		bool		in_recovery;

		res = PQexec(conn, "SELECT pg_catalog.pg_is_in_recovery()");

		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not obtain recovery progress");
			exit(1);
		}

		if (PQntuples(res) != 1)
		{
			pg_log_error("unexpected result from pg_is_in_recovery function");
			exit(1);
		}

		in_recovery = (strcmp(PQgetvalue(res, 0, 0), "t") == 0);

		PQclear(res);

		/*
		 * Does the recovery process finish? In dry run mode, there is no
		 * recovery mode. Bail out as the recovery process has ended.
		 */
		if (!in_recovery || dry_run)
		{
			status = POSTMASTER_READY;
			break;
		}

		/* Keep waiting. */
		pg_usleep(WAIT_INTERVAL * USEC_PER_SEC);
	}

	disconnect_database(conn);

	if (status == POSTMASTER_STILL_STARTING)
	{
		pg_log_error("server did not end recovery");
		exit(1);
	}

	pg_log_info("postmaster reached the consistent state");
}

/*
 * Create a publication that includes all tables in the database.
 */
static void
create_publication(PGconn *conn, LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	/* Check if the publication needs to be created. */
	appendPQExpBuffer(str,
					  "SELECT puballtables FROM pg_catalog.pg_publication WHERE pubname = '%s'",
					  dbinfo->pubname);
	res = PQexec(conn, str->data);
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain publication information: %s",
					 PQresultErrorMessage(res));
		PQclear(res);
		PQfinish(conn);
		exit(1);
	}

	if (PQntuples(res) == 1)
	{
		/*
		 * If publication name already exists and puballtables is true, let's
		 * use it. A previous run of pg_subscriber must have created this
		 * publication. Bail out.
		 */
		if (strcmp(PQgetvalue(res, 0, 0), "t") == 0)
		{
			pg_log_info("publication \"%s\" already exists", dbinfo->pubname);
			return;
		}
		else
		{
			/*
			 * Unfortunately, if it reaches this code path, it will always
			 * fail (unless you decide to change the existing publication
			 * name). That's bad but it is very unlikely that the user will
			 * choose a name with pg_subscriber_ prefix followed by the exact
			 * database oid in which puballtables is false.
			 */
			pg_log_error("publication \"%s\" does not replicate changes for all tables",
						 dbinfo->pubname);
			pg_log_error_hint("Consider renaming this publication.");
			PQclear(res);
			PQfinish(conn);
			exit(1);
		}
	}

	PQclear(res);
	resetPQExpBuffer(str);

	pg_log_info("creating publication \"%s\" on database \"%s\"", dbinfo->pubname, dbinfo->dbname);

	appendPQExpBuffer(str, "CREATE PUBLICATION %s FOR ALL TABLES", dbinfo->pubname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			pg_log_error("could not create publication \"%s\" on database \"%s\": %s",
						 dbinfo->pubname, dbinfo->dbname, PQerrorMessage(conn));
			PQfinish(conn);
			exit(1);
		}
	}

	/* for cleanup purposes */
	dbinfo->made_publication = true;

	if (!dry_run)
		PQclear(res);

	destroyPQExpBuffer(str);
}

/*
 * Remove publication if it couldn't finish all steps.
 */
static void
drop_publication(PGconn *conn, LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("dropping publication \"%s\" on database \"%s\"", dbinfo->pubname, dbinfo->dbname);

	appendPQExpBuffer(str, "DROP PUBLICATION %s", dbinfo->pubname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
			pg_log_error("could not drop publication \"%s\" on database \"%s\": %s", dbinfo->pubname, dbinfo->dbname, PQerrorMessage(conn));

		PQclear(res);
	}

	destroyPQExpBuffer(str);
}

/*
 * Create a subscription with some predefined options.
 *
 * A replication slot was already created in a previous step. Let's use it. By
 * default, the subscription name is used as replication slot name. It is
 * not required to copy data. The subscription will be created but it will not
 * be enabled now. That's because the replication progress must be set and the
 * replication origin name (one of the function arguments) contains the
 * subscription OID in its name. Once the subscription is created,
 * set_replication_progress() can obtain the chosen origin name and set up its
 * initial location.
 */
static void
create_subscription(PGconn *conn, LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("creating subscription \"%s\" on database \"%s\"", dbinfo->subname, dbinfo->dbname);

	appendPQExpBuffer(str,
					  "CREATE SUBSCRIPTION %s CONNECTION '%s' PUBLICATION %s "
					  "WITH (create_slot = false, copy_data = false, enabled = false)",
					  dbinfo->subname, dbinfo->pubconninfo, dbinfo->pubname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			pg_log_error("could not create subscription \"%s\" on database \"%s\": %s",
						 dbinfo->subname, dbinfo->dbname, PQerrorMessage(conn));
			PQfinish(conn);
			exit(1);
		}
	}

	/* for cleanup purposes */
	dbinfo->made_subscription = true;

	if (!dry_run)
		PQclear(res);

	destroyPQExpBuffer(str);
}

/*
 * Remove subscription if it couldn't finish all steps.
 */
static void
drop_subscription(PGconn *conn, LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("dropping subscription \"%s\" on database \"%s\"", dbinfo->subname, dbinfo->dbname);

	appendPQExpBuffer(str, "DROP SUBSCRIPTION %s", dbinfo->subname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
			pg_log_error("could not drop subscription \"%s\" on database \"%s\": %s", dbinfo->subname, dbinfo->dbname, PQerrorMessage(conn));

		PQclear(res);
	}

	destroyPQExpBuffer(str);
}

/*
 * Sets the replication progress to the consistent LSN.
 *
 * The subscriber caught up to the consistent LSN provided by the temporary
 * replication slot. The goal is to set up the initial location for the logical
 * replication that is the exact LSN that the subscriber was promoted. Once the
 * subscription is enabled it will start streaming from that location onwards.
 * In dry run mode, the subscription OID and LSN are set to invalid values for
 * printing purposes.
 */
static void
set_replication_progress(PGconn *conn, LogicalRepInfo *dbinfo, const char *lsn)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;
	Oid			suboid;
	char		originname[NAMEDATALEN];
	char		lsnstr[17 + 1]; /* MAXPG_LSNLEN = 17 */

	Assert(conn != NULL);

	appendPQExpBuffer(str,
					  "SELECT oid FROM pg_catalog.pg_subscription WHERE subname = '%s'", dbinfo->subname);

	res = PQexec(conn, str->data);
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain subscription OID: %s",
					 PQresultErrorMessage(res));
		PQclear(res);
		PQfinish(conn);
		exit(1);
	}

	if (PQntuples(res) != 1 && !dry_run)
	{
		pg_log_error("could not obtain subscription OID: got %d rows, expected %d rows",
					 PQntuples(res), 1);
		PQclear(res);
		PQfinish(conn);
		exit(1);
	}

	if (dry_run)
	{
		suboid = InvalidOid;
		snprintf(lsnstr, sizeof(lsnstr), "%X/%X", LSN_FORMAT_ARGS((XLogRecPtr) InvalidXLogRecPtr));
	}
	else
	{
		suboid = strtoul(PQgetvalue(res, 0, 0), NULL, 10);
		snprintf(lsnstr, sizeof(lsnstr), "%s", lsn);
	}

	/*
	 * The origin name is defined as pg_%u. %u is the subscription OID. See
	 * ApplyWorkerMain().
	 */
	snprintf(originname, sizeof(originname), "pg_%u", suboid);

	PQclear(res);

	pg_log_info("setting the replication progress (node name \"%s\" ; LSN %s) on database \"%s\"",
				originname, lsnstr, dbinfo->dbname);

	resetPQExpBuffer(str);
	appendPQExpBuffer(str,
					  "SELECT pg_catalog.pg_replication_origin_advance('%s', '%s')", originname, lsnstr);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not set replication progress for the subscription \"%s\": %s",
						 dbinfo->subname, PQresultErrorMessage(res));
			PQfinish(conn);
			exit(1);
		}

		PQclear(res);
	}

	destroyPQExpBuffer(str);
}

/*
 * Enables the subscription.
 *
 * The subscription was created in a previous step but it was disabled. After
 * adjusting the initial location, enabling the subscription is the last step
 * of this setup.
 */
static void
enable_subscription(PGconn *conn, LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("enabling subscription \"%s\" on database \"%s\"", dbinfo->subname, dbinfo->dbname);

	appendPQExpBuffer(str, "ALTER SUBSCRIPTION %s ENABLE", dbinfo->subname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			pg_log_error("could not enable subscription \"%s\": %s", dbinfo->subname,
						 PQerrorMessage(conn));
			PQfinish(conn);
			exit(1);
		}

		PQclear(res);
	}

	destroyPQExpBuffer(str);
}

int
main(int argc, char **argv)
{
	static struct option long_options[] =
	{
		{"help", no_argument, NULL, '?'},
		{"version", no_argument, NULL, 'V'},
		{"pgdata", required_argument, NULL, 'D'},
		{"publisher-conninfo", required_argument, NULL, 'P'},
		{"subscriber-conninfo", required_argument, NULL, 'S'},
		{"database", required_argument, NULL, 'd'},
		{"dry-run", no_argument, NULL, 'n'},
		{"verbose", no_argument, NULL, 'v'},
		{NULL, 0, NULL, 0}
	};

	int			c;
	int			option_index;
	int			rc;

	char	   *pg_ctl_cmd;

	char	   *base_dir;
	char	   *server_start_log;

	char		timebuf[128];
	struct timeval time;
	time_t		tt;
	int			len;

	char	   *pub_base_conninfo = NULL;
	char	   *sub_base_conninfo = NULL;
	char	   *dbname_conninfo = NULL;

	uint64		pub_sysid;
	uint64		sub_sysid;
	struct stat statbuf;

	PGconn	   *conn;
	char	   *consistent_lsn;

	PQExpBuffer recoveryconfcontents = NULL;

	char		pidfile[MAXPGPATH];

	int			i;

	pg_logging_init(argv[0]);
	pg_logging_set_level(PG_LOG_WARNING);
	progname = get_progname(argv[0]);
	set_pglocale_pgservice(argv[0], PG_TEXTDOMAIN("pg_subscriber"));

	if (argc > 1)
	{
		if (strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-?") == 0)
		{
			usage();
			exit(0);
		}
		else if (strcmp(argv[1], "-V") == 0
				 || strcmp(argv[1], "--version") == 0)
		{
			puts("pg_subscriber (PostgreSQL) " PG_VERSION);
			exit(0);
		}
	}

	atexit(cleanup_objects_atexit);

	/*
	 * Don't allow it to be run as root. It uses pg_ctl which does not allow
	 * it either.
	 */
#ifndef WIN32
	if (geteuid() == 0)
	{
		pg_log_error("cannot be executed by \"root\"");
		pg_log_error_hint("You must run %s as the PostgreSQL superuser.",
						  progname);
		exit(1);
	}
#endif

	while ((c = getopt_long(argc, argv, "D:P:S:d:nv",
							long_options, &option_index)) != -1)
	{
		switch (c)
		{
			case 'D':
				subscriber_dir = pg_strdup(optarg);
				break;
			case 'P':
				pub_conninfo_str = pg_strdup(optarg);
				break;
			case 'S':
				sub_conninfo_str = pg_strdup(optarg);
				break;
			case 'd':
				/* Ignore duplicated database names. */
				if (!simple_string_list_member(&database_names, optarg))
				{
					simple_string_list_append(&database_names, optarg);
					num_dbs++;
				}
				break;
			case 'n':
				dry_run = true;
				break;
			case 'v':
				pg_logging_increase_verbosity();
				break;
			default:
				/* getopt_long already emitted a complaint */
				pg_log_error_hint("Try \"%s --help\" for more information.", progname);
				exit(1);
		}
	}

	/*
	 * Any non-option arguments?
	 */
	if (optind < argc)
	{
		pg_log_error("too many command-line arguments (first is \"%s\")",
					 argv[optind]);
		pg_log_error_hint("Try \"%s --help\" for more information.", progname);
		exit(1);
	}

	/*
	 * Required arguments
	 */
	if (subscriber_dir == NULL)
	{
		pg_log_error("no subscriber data directory specified");
		pg_log_error_hint("Try \"%s --help\" for more information.", progname);
		exit(1);
	}

	/*
	 * Parse connection string. Build a base connection string that might be
	 * reused by multiple databases.
	 */
	if (pub_conninfo_str == NULL)
	{
		/*
		 * TODO use primary_conninfo (if available) from subscriber and
		 * extract publisher connection string. Assume that there are
		 * identical entries for physical and logical replication. If there is
		 * not, we would fail anyway.
		 */
		pg_log_error("no publisher connection string specified");
		pg_log_error_hint("Try \"%s --help\" for more information.", progname);
		exit(1);
	}
	pub_base_conninfo = get_base_conninfo(pub_conninfo_str, dbname_conninfo,
										  "publisher");
	if (pub_base_conninfo == NULL)
		exit(1);

	if (sub_conninfo_str == NULL)
	{
		pg_log_error("no subscriber connection string specified");
		pg_log_error_hint("Try \"%s --help\" for more information.", progname);
		exit(1);
	}
	sub_base_conninfo = get_base_conninfo(sub_conninfo_str, NULL, "subscriber");
	if (sub_base_conninfo == NULL)
		exit(1);

	if (database_names.head == NULL)
	{
		pg_log_info("no database was specified");

		/*
		 * If --database option is not provided, try to obtain the dbname from
		 * the publisher conninfo. If dbname parameter is not available, error
		 * out.
		 */
		if (dbname_conninfo)
		{
			simple_string_list_append(&database_names, dbname_conninfo);
			num_dbs++;

			pg_log_info("database \"%s\" was extracted from the publisher connection string",
						dbname_conninfo);
		}
		else
		{
			pg_log_error("no database name specified");
			pg_log_error_hint("Try \"%s --help\" for more information.", progname);
			exit(1);
		}
	}

	/*
	 * Get the absolute path of pg_ctl and pg_resetwal on the subscriber.
	 */
	if (!get_exec_path(argv[0]))
		exit(1);

	/* rudimentary check for a data directory. */
	if (!check_data_directory(subscriber_dir))
		exit(1);

	/* Store database information for publisher and subscriber. */
	dbinfo = store_pub_sub_info(pub_base_conninfo, sub_base_conninfo);

	/*
	 * Check if the subscriber data directory has the same system identifier
	 * than the publisher data directory.
	 */
	pub_sysid = get_sysid_from_conn(dbinfo[0].pubconninfo);
	sub_sysid = get_control_from_datadir(subscriber_dir);
	if (pub_sysid != sub_sysid)
	{
		pg_log_error("subscriber data directory is not a copy of the source database cluster");
		exit(1);
	}

	/*
	 * Create the output directory to store any data generated by this tool.
	 */
	base_dir = (char *) pg_malloc0(MAXPGPATH);
	len = snprintf(base_dir, MAXPGPATH, "%s/%s", subscriber_dir, PGS_OUTPUT_DIR);
	if (len >= MAXPGPATH)
	{
		pg_log_error("directory path for subscriber is too long");
		exit(1);
	}

	if (mkdir(base_dir, pg_dir_create_mode) < 0 && errno != EEXIST)
	{
		pg_log_error("could not create directory \"%s\": %m", base_dir);
		exit(1);
	}

	/* subscriber PID file. */
	snprintf(pidfile, MAXPGPATH, "%s/postmaster.pid", subscriber_dir);

	/*
	 * Stop the subscriber if it is a standby server. Before executing the
	 * transformation steps, make sure the subscriber is not running because
	 * one of the steps is to modify some recovery parameters that require a
	 * restart.
	 */
	if (stat(pidfile, &statbuf) == 0)
	{
		/*
		 * Since the standby server is running, check if it is using an
		 * existing replication slot for WAL retention purposes. This
		 * replication slot has no use after the transformation, hence, it
		 * will be removed at the end of this process.
		 */
		primary_slot_name = use_primary_slot_name();
		if (primary_slot_name != NULL)
			pg_log_info("primary has replication slot \"%s\"", primary_slot_name);

		pg_log_info("subscriber is up and running");
		pg_log_info("stopping the server to start the transformation steps");

		pg_ctl_cmd = psprintf("\"%s\" stop -D \"%s\" -s", pg_ctl_path, subscriber_dir);
		rc = system(pg_ctl_cmd);
		pg_ctl_status(pg_ctl_cmd, rc, 0);
	}

	/*
	 * Create a replication slot for each database on the publisher.
	 */
	if (!create_all_logical_replication_slots(dbinfo))
		exit(1);

	/*
	 * Create a logical replication slot to get a consistent LSN.
	 *
	 * This consistent LSN will be used later to advanced the recently created
	 * replication slots. We cannot use the last created replication slot
	 * because the consistent LSN should be obtained *after* the base backup
	 * finishes (and the base backup should include the logical replication
	 * slots).
	 *
	 * XXX we should probably use the last created replication slot to get a
	 * consistent LSN but it should be changed after adding pg_basebackup
	 * support.
	 *
	 * A temporary replication slot is not used here to avoid keeping a
	 * replication connection open (depending when base backup was taken, the
	 * connection should be open for a few hours).
	 */
	conn = connect_database(dbinfo[0].pubconninfo);
	if (conn == NULL)
		exit(1);
	consistent_lsn = create_logical_replication_slot(conn, &dbinfo[0],
													 temp_replslot);

	/*
	 * Write recovery parameters.
	 *
	 * Despite of the recovery parameters will be written to the subscriber,
	 * use a publisher connection for the follwing recovery functions. The
	 * connection is only used to check the current server version (physical
	 * replica, same server version). The subscriber is not running yet. In
	 * dry run mode, the recovery parameters *won't* be written. An invalid
	 * LSN is used for printing purposes.
	 */
	recoveryconfcontents = GenerateRecoveryConfig(conn, NULL);
	appendPQExpBuffer(recoveryconfcontents, "recovery_target_inclusive = true\n");
	appendPQExpBuffer(recoveryconfcontents, "recovery_target_action = promote\n");

	if (dry_run)
	{
		appendPQExpBuffer(recoveryconfcontents, "# dry run mode");
		appendPQExpBuffer(recoveryconfcontents, "recovery_target_lsn = '%X/%X'\n",
						  LSN_FORMAT_ARGS((XLogRecPtr) InvalidXLogRecPtr));
	}
	else
	{
		appendPQExpBuffer(recoveryconfcontents, "recovery_target_lsn = '%s'\n",
						  consistent_lsn);
		WriteRecoveryConfig(conn, subscriber_dir, recoveryconfcontents);
	}
	disconnect_database(conn);

	pg_log_debug("recovery parameters:\n%s", recoveryconfcontents->data);

	/*
	 * Start subscriber and wait until accepting connections.
	 */
	pg_log_info("starting the subscriber");

	/* append timestamp with ISO 8601 format. */
	gettimeofday(&time, NULL);
	tt = (time_t) time.tv_sec;
	strftime(timebuf, sizeof(timebuf), "%Y%m%dT%H%M%S", localtime(&tt));
	snprintf(timebuf + strlen(timebuf), sizeof(timebuf) - strlen(timebuf),
			 ".%03d", (int) (time.tv_usec / 1000));

	server_start_log = (char *) pg_malloc0(MAXPGPATH);
	len = snprintf(server_start_log, MAXPGPATH, "%s/%s/server_start_%s.log", subscriber_dir, PGS_OUTPUT_DIR, timebuf);
	if (len >= MAXPGPATH)
	{
		pg_log_error("log file path is too long");
		exit(1);
	}

	pg_ctl_cmd = psprintf("\"%s\" start -D \"%s\" -s -l \"%s\"", pg_ctl_path, subscriber_dir, server_start_log);
	rc = system(pg_ctl_cmd);
	pg_ctl_status(pg_ctl_cmd, rc, 1);

	/*
	 * Waiting the subscriber to be promoted.
	 */
	wait_for_end_recovery(dbinfo[0].subconninfo);

	/*
	 * Create a publication for each database. This step should be executed
	 * after promoting the subscriber to avoid replicating unnecessary
	 * objects.
	 */
	for (i = 0; i < num_dbs; i++)
	{
		char		pubname[NAMEDATALEN];

		/* Connect to publisher. */
		conn = connect_database(dbinfo[i].pubconninfo);
		if (conn == NULL)
			exit(1);

		/*
		 * Build the publication name. The name must not exceed NAMEDATALEN -
		 * 1. This current schema uses a maximum of 35 characters (14 + 10 +
		 * '\0').
		 */
		snprintf(pubname, sizeof(pubname), "pg_subscriber_%u", dbinfo[i].oid);
		dbinfo[i].pubname = pg_strdup(pubname);

		create_publication(conn, &dbinfo[i]);

		disconnect_database(conn);
	}

	/*
	 * Create a subscription for each database.
	 */
	for (i = 0; i < num_dbs; i++)
	{
		/* Connect to subscriber. */
		conn = connect_database(dbinfo[i].subconninfo);
		if (conn == NULL)
			exit(1);

		create_subscription(conn, &dbinfo[i]);

		/* Set the replication progress to the correct LSN. */
		set_replication_progress(conn, &dbinfo[i], consistent_lsn);

		/* Enable subscription. */
		enable_subscription(conn, &dbinfo[i]);

		disconnect_database(conn);
	}

	/*
	 * The transient replication slot is no longer required. Drop it.
	 *
	 * If the physical replication slot exists, drop it.
	 *
	 * XXX we might not fail here. Instead, we provide a warning so the user
	 * eventually drops the replication slot later.
	 */
	conn = connect_database(dbinfo[0].pubconninfo);
	if (conn == NULL)
	{
		pg_log_warning("could not drop transient replication slot \"%s\" on publisher", temp_replslot);
		pg_log_warning_hint("Drop this replication slot soon to avoid retention of WAL files.");
		if (primary_slot_name != NULL)
			pg_log_warning("could not drop replication slot \"%s\" on primary", primary_slot_name);
	}
	else
	{
		drop_replication_slot(conn, &dbinfo[0], temp_replslot);
		if (primary_slot_name != NULL)
			drop_replication_slot(conn, &dbinfo[0], primary_slot_name);
		disconnect_database(conn);
	}

	/*
	 * Stop the subscriber.
	 */
	pg_log_info("stopping the subscriber");

	pg_ctl_cmd = psprintf("\"%s\" stop -D \"%s\" -s", pg_ctl_path, subscriber_dir);
	rc = system(pg_ctl_cmd);
	pg_ctl_status(pg_ctl_cmd, rc, 0);

	/*
	 * Change system identifier.
	 */
	modify_sysid(pg_resetwal_path, subscriber_dir);

	/*
	 * Remove log file generated by this tool, if it runs successfully.
	 * Otherwise, file is kept that may provide useful debugging information.
	 */
	unlink(server_start_log);

	success = true;

	pg_log_info("Done!");

	return 0;
}
