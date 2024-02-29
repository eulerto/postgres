/*-------------------------------------------------------------------------
 *
 * pg_createsubscriber.c
 *	  Create a new logical replica from a standby server
 *
 * Copyright (C) 2024, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *	  src/bin/pg_basebackup/pg_createsubscriber.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres_fe.h"

#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>

#include "catalog/pg_authid_d.h"
#include "common/connect.h"
#include "common/controldata_utils.h"
#include "common/file_perm.h"
#include "common/logging.h"
#include "common/restricted_token.h"
#include "common/username.h"
#include "fe_utils/recovery_gen.h"
#include "fe_utils/simple_list.h"
#include "getopt_long.h"

#define	DEFAULT_SUB_PORT	50432
#define	BASE_OUTPUT_DIR		"pg_createsubscriber_output.d"

/* Command-line options */
struct CreateSubscriberOptions
{
	char	   *subscriber_dir; /* standby/subscriber data directory */
	char	   *pub_conninfo_str;	/* publisher connection string */
	char	   *socket_dir;			/* directory for Unix-domain socket, if any */
	unsigned short	sub_port;		/* subscriber port number */
	const char	   *sub_username;	/* subscriber username */
	SimpleStringList database_names;	/* list of database names */
	bool		retain;			/* retain log file? */
	int			recovery_timeout;	/* stop recovery after this time */
} CreateSubscriberOptions;

struct LogicalRepInfo
{
	Oid			oid;			/* database OID */
	char	   *dbname;			/* database name */
	char	   *pubconninfo;	/* publisher connection string */
	char	   *subconninfo;	/* subscriber connection string */
	char	   *pubname;		/* publication name */
	char	   *subname;		/* subscription name / replication slot name */

	bool		made_replslot;	/* replication slot was created */
	bool		made_publication;	/* publication was created */
} LogicalRepInfo;

static void cleanup_objects_atexit(void);
static void usage();
static char *get_base_conninfo(char *conninfo, char **dbname);
static char *get_exec_path(const char *argv0, const char *progname);
static void check_data_directory(const char *datadir);
static char *concat_conninfo_dbname(const char *conninfo, const char *dbname);
static struct LogicalRepInfo *store_pub_sub_info(SimpleStringList dbnames,
										  const char *pub_base_conninfo,
										  const char *sub_base_conninfo);
static PGconn *connect_database(const char *conninfo, bool exit_on_error);
static void disconnect_database(PGconn *conn, bool exit_on_error);
static uint64 get_primary_sysid(const char *conninfo);
static uint64 get_standby_sysid(const char *datadir);
static void modify_subscriber_sysid(const char *pg_resetwal_path,
									struct CreateSubscriberOptions *opt);
static bool server_is_in_recovery(PGconn *conn);
static void check_publisher(struct LogicalRepInfo *dbinfo);
static void setup_publisher(struct LogicalRepInfo *dbinfo);
static void check_subscriber(struct LogicalRepInfo *dbinfo);
static void setup_subscriber(struct LogicalRepInfo *dbinfo,
							 const char *consistent_lsn);
static char *create_logical_replication_slot(PGconn *conn,
											 struct LogicalRepInfo *dbinfo,
											 bool temporary);
static void drop_replication_slot(PGconn *conn, struct LogicalRepInfo *dbinfo,
								  const char *slot_name);
static char *setup_server_logfile(const char *datadir);
static void pg_ctl_status(const char *pg_ctl_cmd, int rc);
static void start_standby_server(struct CreateSubscriberOptions *opt,
								 const char *pg_ctl_path, const char *logfile);
static void stop_standby_server(const char *pg_ctl_path, const char *datadir);
static void wait_for_end_recovery(const char *conninfo, const char *pg_ctl_path,
								  struct CreateSubscriberOptions *opt);
static void create_publication(PGconn *conn, struct LogicalRepInfo *dbinfo);
static void drop_publication(PGconn *conn, struct LogicalRepInfo *dbinfo);
static void create_subscription(PGconn *conn, struct LogicalRepInfo *dbinfo);
static void set_replication_progress(PGconn *conn, struct LogicalRepInfo *dbinfo,
									 const char *lsn);
static void enable_subscription(PGconn *conn, struct LogicalRepInfo *dbinfo);

#define	USEC_PER_SEC	1000000
#define	WAIT_INTERVAL	1		/* 1 second */

static const char *progname;

static char *primary_slot_name = NULL;
static bool dry_run = false;

static bool success = false;

static struct LogicalRepInfo *dbinfo;
static int	num_dbs = 0;

static bool recovery_ended = false;

enum WaitPMResult
{
	POSTMASTER_READY,
	POSTMASTER_STILL_STARTING
};


/*
 * Cleanup objects that were created by pg_createsubscriber if there is an
 * error.
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
		if (recovery_ended)
		{
			pg_log_warning("pg_createsubscriber failed after the end of recovery");
			pg_log_warning_hint("The target server cannot be used as a physical replica anymore.");
			pg_log_warning_hint("You must recreate the physical replica before continuing.");
		}

		if (dbinfo[i].made_publication || dbinfo[i].made_replslot)
		{
			conn = connect_database(dbinfo[i].pubconninfo, false);
			if (conn != NULL)
			{
				if (dbinfo[i].made_publication)
					drop_publication(conn, &dbinfo[i]);
				if (dbinfo[i].made_replslot)
					drop_replication_slot(conn, &dbinfo[i], dbinfo[i].subname);
				disconnect_database(conn, false);
			}
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
	printf(_(" -d, --database=DBNAME               database to create a subscription\n"));
	printf(_(" -D, --pgdata=DATADIR                location for the subscriber data directory\n"));
	printf(_(" -n, --dry-run                       dry run, just show what would be done\n"));
	printf(_(" -p, --subscriber-port=PORT          subscriber port number (default %d)\n"), DEFAULT_SUB_PORT);
	printf(_(" -P, --publisher-server=CONNSTR      publisher connection string\n"));
	printf(_(" -r, --retain                        retain log file after success\n"));
	printf(_(" -s, --socket-directory=DIR          socket directory to use (default current directory)\n"));
	printf(_(" -t, --recovery-timeout=SECS         seconds to wait for recovery to end\n"));
	printf(_(" -U, --subscriber-username=NAME      subscriber username\n"));
	printf(_(" -v, --verbose                       output verbose messages\n"));
	printf(_(" -V, --version                       output version information, then exit\n"));
	printf(_(" -?, --help                          show this help, then exit\n"));
	printf(_("\nReport bugs to <%s>.\n"), PACKAGE_BUGREPORT);
	printf(_("%s home page: <%s>\n"), PACKAGE_NAME, PACKAGE_URL);
}

/*
 * Validate a connection string. Returns a base connection string that is a
 * connection string without a database name.
 *
 * Since we might process multiple databases, each database name will be
 * appended to this base connection string to provide a final connection
 * string. If the second argument (dbname) is not null, returns dbname if the
 * provided connection string contains it. If option --database is not
 * provided, uses dbname as the only database to setup the logical replica.
 *
 * It is the caller's responsibility to free the returned connection string and
 * dbname.
 */
static char *
get_base_conninfo(char *conninfo, char **dbname)
{
	PQExpBuffer buf = createPQExpBuffer();
	PQconninfoOption *conn_opts = NULL;
	PQconninfoOption *conn_opt;
	char	   *errmsg = NULL;
	char	   *ret;
	int			i;

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
				*dbname = pg_strdup(conn_opt->val);
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

	ret = pg_strdup(buf->data);

	destroyPQExpBuffer(buf);
	PQconninfoFree(conn_opts);

	return ret;
}

/*
 * Verify if a PostgreSQL binary (progname) is available in the same directory as
 * pg_createsubscriber and it has the same version.  It returns the absolute
 * path of the progname.
 */
static char *
get_exec_path(const char *argv0, const char *progname)
{
	char	   *versionstr;
	char	   *exec_path;
	int			ret;

	versionstr = psprintf("%s (PostgreSQL) %s\n", progname, PG_VERSION);
	exec_path = pg_malloc(MAXPGPATH);
	ret = find_other_exec(argv0, progname, versionstr, exec_path);

	if (ret < 0)
	{
		char		full_path[MAXPGPATH];

		if (find_my_exec(argv0, full_path) < 0)
			strlcpy(full_path, progname, sizeof(full_path));

		if (ret == -1)
			pg_fatal("program \"%s\" is needed by %s but was not found in the same directory as \"%s\"",
					 progname, "pg_createsubscriber", full_path);
		else
			pg_fatal("program \"%s\" was found by \"%s\" but was not the same version as %s",
					 progname, full_path, "pg_createsubscriber");
	}

	pg_log_debug("%s path is:  %s", progname, exec_path);

	return exec_path;
}

/*
 * Is it a cluster directory? These are preliminary checks. It is far from
 * making an accurate check. If it is not a clone from the publisher, it will
 * eventually fail in a future step.
 */
static void
check_data_directory(const char *datadir)
{
	struct stat statbuf;
	char		versionfile[MAXPGPATH];

	pg_log_info("checking if directory \"%s\" is a cluster data directory",
				datadir);

	if (stat(datadir, &statbuf) != 0)
	{
		if (errno == ENOENT)
			pg_fatal("data directory \"%s\" does not exist", datadir);
		else
			pg_fatal("could not access directory \"%s\": %s", datadir,
						 strerror(errno));
	}

	snprintf(versionfile, MAXPGPATH, "%s/PG_VERSION", datadir);
	if (stat(versionfile, &statbuf) != 0 && errno == ENOENT)
	{
		pg_fatal("directory \"%s\" is not a database cluster directory",
					 datadir);
	}
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
static struct LogicalRepInfo *
store_pub_sub_info(SimpleStringList dbnames, const char *pub_base_conninfo,
				   const char *sub_base_conninfo)
{
	struct LogicalRepInfo *dbinfo;
	int			i = 0;

	dbinfo = (struct LogicalRepInfo *) pg_malloc(num_dbs * sizeof(struct LogicalRepInfo));

	for (SimpleStringListCell *cell = dbnames.head; cell; cell = cell->next)
	{
		char	   *conninfo;

		/* Fill publisher attributes */
		conninfo = concat_conninfo_dbname(pub_base_conninfo, cell->val);
		dbinfo[i].pubconninfo = conninfo;
		dbinfo[i].dbname = cell->val;
		dbinfo[i].made_replslot = false;
		dbinfo[i].made_publication = false;
		/* Fill subscriber attributes */
		conninfo = concat_conninfo_dbname(sub_base_conninfo, cell->val);
		dbinfo[i].subconninfo = conninfo;
		/* Other fields will be filled later */

		pg_log_debug("publisher(%d): connection string: %s", i, dbinfo[i].pubconninfo);
		pg_log_debug("subscriber(%d): connection string: %s", i, dbinfo[i].subconninfo);

		i++;
	}

	return dbinfo;
}

/*
 * Open a new connection. If exit_on_error is true, it has an undesired
 * condition and it should exit immediately.
 */
static PGconn *
connect_database(const char *conninfo, bool exit_on_error)
{
	PGconn	   *conn;
	PGresult   *res;

	conn = PQconnectdb(conninfo);
	if (PQstatus(conn) != CONNECTION_OK)
	{
		pg_log_error("connection to database failed: %s",
					 PQerrorMessage(conn));
		if (exit_on_error)
			exit(1);

		return NULL;
	}

	/* Secure search_path */
	res = PQexec(conn, ALWAYS_SECURE_SEARCH_PATH_SQL);
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not clear search_path: %s",
					 PQresultErrorMessage(res));
		if (exit_on_error)
			exit(1);

		return NULL;
	}
	PQclear(res);

	return conn;
}

/*
 * Close the connection. If exit_on_error is true, it has an undesired
 * condition and it should exit immediately.
 */
static void
disconnect_database(PGconn *conn, bool exit_on_error)
{
	Assert(conn != NULL);

	PQfinish(conn);

	if (exit_on_error)
		exit(1);
}

/*
 * Obtain the system identifier using the provided connection. It will be used
 * to compare if a data directory is a clone of another one.
 */
static uint64
get_primary_sysid(const char *conninfo)
{
	PGconn	   *conn;
	PGresult   *res;
	uint64		sysid;

	pg_log_info("getting system identifier from publisher");

	conn = connect_database(conninfo, true);

	res = PQexec(conn, "SELECT system_identifier FROM pg_catalog.pg_control_system()");
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not get system identifier: %s",
				 PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}
	if (PQntuples(res) != 1)
	{
		pg_log_error("could not get system identifier: got %d rows, expected %d row",
				 PQntuples(res), 1);
		disconnect_database(conn, true);
	}

	sysid = strtou64(PQgetvalue(res, 0, 0), NULL, 10);

	pg_log_info("system identifier is %llu on publisher",
				(unsigned long long) sysid);

	PQclear(res);
	disconnect_database(conn, false);

	return sysid;
}

/*
 * Obtain the system identifier from control file. It will be used to compare
 * if a data directory is a clone of another one. This routine is used locally
 * and avoids a connection.
 */
static uint64
get_standby_sysid(const char *datadir)
{
	ControlFileData *cf;
	bool		crc_ok;
	uint64		sysid;

	pg_log_info("getting system identifier from subscriber");

	cf = get_controlfile(datadir, &crc_ok);
	if (!crc_ok)
		pg_fatal("control file appears to be corrupt");

	sysid = cf->system_identifier;

	pg_log_info("system identifier is %llu on subscriber",
				(unsigned long long) sysid);

	pg_free(cf);

	return sysid;
}

/*
 * Modify the system identifier. Since a standby server preserves the system
 * identifier, it makes sense to change it to avoid situations in which WAL
 * files from one of the systems might be used in the other one.
 */
static void
modify_subscriber_sysid(const char *pg_resetwal_path, struct CreateSubscriberOptions *opt)
{
	ControlFileData *cf;
	bool		crc_ok;
	struct timeval tv;

	char	   *cmd_str;

	pg_log_info("modifying system identifier from subscriber");

	cf = get_controlfile(opt->subscriber_dir, &crc_ok);
	if (!crc_ok)
		pg_fatal("control file appears to be corrupt");

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
		update_controlfile(opt->subscriber_dir, cf, true);

	pg_log_info("system identifier is %llu on subscriber",
				(unsigned long long) cf->system_identifier);

	pg_log_info("running pg_resetwal on the subscriber");

	cmd_str = psprintf("\"%s\" -D \"%s\" > \"%s\"", pg_resetwal_path,
					   opt->subscriber_dir, DEVNULL);

	pg_log_debug("command is: %s", cmd_str);

	if (!dry_run)
	{
		int rc = system(cmd_str);
		if (rc == 0)
			pg_log_info("subscriber successfully changed the system identifier");
		else
			pg_fatal("subscriber failed to change system identifier: exit code: %d", rc);
	}

	pg_free(cf);
}

/*
 * Create the publications and replication slots in preparation for logical
 * replication.
 */
static void
setup_publisher(struct LogicalRepInfo *dbinfo)
{
	for (int i = 0; i < num_dbs; i++)
	{
		PGconn	   *conn;
		PGresult   *res;
		char		pubname[NAMEDATALEN];
		char		replslotname[NAMEDATALEN];

		conn = connect_database(dbinfo[i].pubconninfo, true);

		res = PQexec(conn,
					 "SELECT oid FROM pg_catalog.pg_database "
					 "WHERE datname = pg_catalog.current_database()");
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not obtain database OID: %s",
						 PQresultErrorMessage(res));
			disconnect_database(conn, true);
		}

		if (PQntuples(res) != 1)
		{
			pg_log_error("could not obtain database OID: got %d rows, expected %d rows",
						 PQntuples(res), 1);
			disconnect_database(conn, true);
		}

		/* Remember database OID */
		dbinfo[i].oid = strtoul(PQgetvalue(res, 0, 0), NULL, 10);

		PQclear(res);

		/*
		 * Build the publication name. The name must not exceed NAMEDATALEN -
		 * 1. This current schema uses a maximum of 31 characters (20 + 10 +
		 * '\0').
		 */
		snprintf(pubname, sizeof(pubname), "pg_createsubscriber_%u",
				 dbinfo[i].oid);
		dbinfo[i].pubname = pg_strdup(pubname);

		/*
		 * Create publication on publisher. This step should be executed
		 * *before* promoting the subscriber to avoid any transactions between
		 * consistent LSN and the new publication rows (such transactions
		 * wouldn't see the new publication rows resulting in an error).
		 */
		create_publication(conn, &dbinfo[i]);

		/*
		 * Build the replication slot name. The name must not exceed
		 * NAMEDATALEN - 1. This current schema uses a maximum of 42
		 * characters (20 + 10 + 1 + 10 + '\0'). PID is included to reduce the
		 * probability of collision. By default, subscription name is used as
		 * replication slot name.
		 */
		snprintf(replslotname, sizeof(replslotname),
				 "pg_createsubscriber_%u_%d",
				 dbinfo[i].oid,
				 (int) getpid());
		dbinfo[i].subname = pg_strdup(replslotname);

		/* Create replication slot on publisher */
		if (create_logical_replication_slot(conn, &dbinfo[i], false) != NULL ||
			dry_run)
			pg_log_info("create replication slot \"%s\" on publisher",
						replslotname);
		else
			exit(1);

		disconnect_database(conn, false);
	}
}

/*
 * Is recovery still in progress?
 */
static bool
server_is_in_recovery(PGconn *conn)
{
	PGresult   *res;
	int			ret;

	res = PQexec(conn, "SELECT pg_catalog.pg_is_in_recovery()");

	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain recovery progress: %s",
					PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}


	ret = strcmp("t", PQgetvalue(res, 0, 0));

	PQclear(res);

	return ret == 0;
}

/*
 * Is the primary server ready for logical replication?
 */
static void
check_publisher(struct LogicalRepInfo *dbinfo)
{
	PGconn	   *conn;
	PGresult   *res;

	char	   *wal_level;
	int			max_repslots;
	int			cur_repslots;
	int			max_walsenders;
	int			cur_walsenders;

	pg_log_info("checking settings on publisher");

	conn = connect_database(dbinfo[0].pubconninfo, true);

	/*
	 * If the primary server is in recovery (i.e. cascading replication),
	 * objects (publication) cannot be created because it is read only.
	 */
	if (server_is_in_recovery(conn))
	{
		pg_log_error("primary server cannot be in recovery");
		disconnect_database(conn, true);
	}

	/*------------------------------------------------------------------------
	 * Logical replication requires a few parameters to be set on publisher.
	 * Since these parameters are not a requirement for physical replication,
	 * we should check it to make sure it won't fail.
	 *
	 * - wal_level = logical
	 * - max_replication_slots >= current + number of dbs to be converted +
	 *                            one temporary logical replication slot
	 * - max_wal_senders >= current + number of dbs to be converted
	 * -----------------------------------------------------------------------
	 */
	res = PQexec(conn,
				 "WITH wl AS "
				 "(SELECT setting AS wallevel FROM pg_catalog.pg_settings "
				 "WHERE name = 'wal_level'), "
				 "total_mrs AS "
				 "(SELECT setting AS tmrs FROM pg_catalog.pg_settings "
				 "WHERE name = 'max_replication_slots'), "
				 "cur_mrs AS "
				 "(SELECT count(*) AS cmrs "
				 "FROM pg_catalog.pg_replication_slots), "
				 "total_mws AS "
				 "(SELECT setting AS tmws FROM pg_catalog.pg_settings "
				 "WHERE name = 'max_wal_senders'), "
				 "cur_mws AS "
				 "(SELECT count(*) AS cmws FROM pg_catalog.pg_stat_activity "
				 "WHERE backend_type = 'walsender') "
				 "SELECT wallevel, tmrs, cmrs, tmws, cmws "
				 "FROM wl, total_mrs, cur_mrs, total_mws, cur_mws");

	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain publisher settings: %s",
					 PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}

	wal_level = strdup(PQgetvalue(res, 0, 0));
	max_repslots = atoi(PQgetvalue(res, 0, 1));
	cur_repslots = atoi(PQgetvalue(res, 0, 2));
	max_walsenders = atoi(PQgetvalue(res, 0, 3));
	cur_walsenders = atoi(PQgetvalue(res, 0, 4));

	PQclear(res);

	pg_log_debug("publisher: wal_level: %s", wal_level);
	pg_log_debug("publisher: max_replication_slots: %d", max_repslots);
	pg_log_debug("publisher: current replication slots: %d", cur_repslots);
	pg_log_debug("publisher: max_wal_senders: %d", max_walsenders);
	pg_log_debug("publisher: current wal senders: %d", cur_walsenders);

	/*
	 * If standby sets primary_slot_name, check if this replication slot is in
	 * use on primary for WAL retention purposes. This replication slot has no
	 * use after the transformation, hence, it will be removed at the end of
	 * this process.
	 */
	if (primary_slot_name)
	{
		PQExpBuffer str = createPQExpBuffer();

		appendPQExpBuffer(str,
						  "SELECT 1 FROM pg_catalog.pg_replication_slots "
						  "WHERE active AND slot_name = '%s'",
						  primary_slot_name);

		pg_log_debug("command is: %s", str->data);

		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not obtain replication slot information: %s",
						 PQresultErrorMessage(res));
			disconnect_database(conn, true);
		}

		if (PQntuples(res) != 1)
		{
			pg_log_error("could not obtain replication slot information: got %d rows, expected %d row",
						 PQntuples(res), 1);
			disconnect_database(conn, true);
		}
		else
			pg_log_info("primary has replication slot \"%s\"",
						primary_slot_name);

		PQclear(res);
	}

	disconnect_database(conn, false);

	if (strcmp(wal_level, "logical") != 0)
		pg_fatal("publisher requires wal_level >= logical");

	/* One additional temporary logical replication slot */
	if (max_repslots - cur_repslots < num_dbs + 1)
	{
		pg_log_error("publisher requires %d replication slots, but only %d remain",
					 num_dbs + 1, max_repslots - cur_repslots);
		pg_log_error_hint("Consider increasing max_replication_slots to at least %d.",
						  cur_repslots + num_dbs + 1);
		exit(1);
	}

	if (max_walsenders - cur_walsenders < num_dbs)
	{
		pg_log_error("publisher requires %d wal sender processes, but only %d remain",
					 num_dbs, max_walsenders - cur_walsenders);
		pg_log_error_hint("Consider increasing max_wal_senders to at least %d.",
						  cur_walsenders + num_dbs);
		exit(1);
	}
}

/*
 * Is the standby server ready for logical replication?
 */
static void
check_subscriber(struct LogicalRepInfo *dbinfo)
{
	PGconn	   *conn;
	PGresult   *res;
	PQExpBuffer str = createPQExpBuffer();

	int			max_lrworkers;
	int			max_repslots;
	int			max_wprocs;

	pg_log_info("checking settings on subscriber");

	conn = connect_database(dbinfo[0].subconninfo, true);

	/* The target server must be a standby */
	if (!server_is_in_recovery(conn))
	{
		pg_log_error("The target server must be a standby");
		disconnect_database(conn, true);
	}

	/*
	 * The target server must not be a primary. The reason is that the system
	 * identifier is modified by pg_resetwal in one of the last steps. Since
	 * physical replication requires same system identifier, replication will
	 * break as soon as the system identifier is changed on the target server.
	 */
	res = PQexec(conn,
			"SELECT 1 FROM pg_catalog.pg_stat_activity "
			"WHERE backend_type = 'walsender'");
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain activity of server processes: %s",
				PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}

	if (PQntuples(res) > 0)
	{
		pg_log_error("target server is a primary");
		pg_log_error_hint("The target server must not have a standby server. Stop it before continuing.");
		disconnect_database(conn, true);
	}

	/*
	 * Subscriptions can only be created by roles that have the privileges of
	 * pg_create_subscription role and CREATE privileges on the specified
	 * database.
	 */
	appendPQExpBuffer(str,
					  "SELECT pg_catalog.pg_has_role(current_user, %u, 'MEMBER'), "
					  "pg_catalog.has_database_privilege(current_user, '%s', 'CREATE'), "
					  "pg_catalog.has_function_privilege(current_user, 'pg_catalog.pg_replication_origin_advance(text, pg_lsn)', 'EXECUTE')",
					  ROLE_PG_CREATE_SUBSCRIPTION, dbinfo[0].dbname);

	pg_log_debug("command is: %s", str->data);

	res = PQexec(conn, str->data);

	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain access privilege information: %s",
					 PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}

	if (strcmp(PQgetvalue(res, 0, 0), "t") != 0)
	{
		pg_log_error("permission denied to create subscription");
		pg_log_error_hint("Only roles with privileges of the \"%s\" role may create subscriptions.",
						  "pg_create_subscription");
		disconnect_database(conn, true);
	}
	if (strcmp(PQgetvalue(res, 0, 1), "t") != 0)
	{
		pg_log_error("permission denied for database %s", dbinfo[0].dbname);
		disconnect_database(conn, true);
	}
	if (strcmp(PQgetvalue(res, 0, 2), "t") != 0)
	{
		pg_log_error("permission denied for function \"%s\"",
					 "pg_catalog.pg_replication_origin_advance(text, pg_lsn)");
		disconnect_database(conn, true);
	}

	destroyPQExpBuffer(str);
	PQclear(res);

	/*------------------------------------------------------------------------
	 * Logical replication requires a few parameters to be set on subscriber.
	 * Since these parameters are not a requirement for physical replication,
	 * we should check it to make sure it won't fail.
	 *
	 * - max_replication_slots >= number of dbs to be converted
	 * - max_logical_replication_workers >= number of dbs to be converted
	 * - max_worker_processes >= 1 + number of dbs to be converted
	 *------------------------------------------------------------------------
	 */
	res = PQexec(conn,
				 "SELECT setting FROM pg_catalog.pg_settings WHERE name IN ("
				 "'max_logical_replication_workers', "
				 "'max_replication_slots', "
				 "'max_worker_processes', "
				 "'primary_slot_name') "
				 "ORDER BY name");

	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain subscriber settings: %s",
					 PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}

	max_lrworkers = atoi(PQgetvalue(res, 0, 0));
	max_repslots = atoi(PQgetvalue(res, 1, 0));
	max_wprocs = atoi(PQgetvalue(res, 2, 0));
	if (strcmp(PQgetvalue(res, 3, 0), "") != 0)
		primary_slot_name = pg_strdup(PQgetvalue(res, 3, 0));

	pg_log_debug("subscriber: max_logical_replication_workers: %d",
				 max_lrworkers);
	pg_log_debug("subscriber: max_replication_slots: %d", max_repslots);
	pg_log_debug("subscriber: max_worker_processes: %d", max_wprocs);
	if (primary_slot_name)
		pg_log_debug("subscriber: primary_slot_name: %s", primary_slot_name);

	PQclear(res);

	disconnect_database(conn, false);

	if (max_repslots < num_dbs)
	{
		pg_log_error("subscriber requires %d replication slots, but only %d remain",
					 num_dbs, max_repslots);
		pg_log_error_hint("Consider increasing max_replication_slots to at least %d.",
						  num_dbs);
		disconnect_database(conn, true);
	}

	if (max_lrworkers < num_dbs)
	{
		pg_log_error("subscriber requires %d logical replication workers, but only %d remain",
					 num_dbs, max_lrworkers);
		pg_log_error_hint("Consider increasing max_logical_replication_workers to at least %d.",
						  num_dbs);
		disconnect_database(conn, true);
	}

	if (max_wprocs < num_dbs + 1)
	{
		pg_log_error("subscriber requires %d worker processes, but only %d remain",
					 num_dbs + 1, max_wprocs);
		pg_log_error_hint("Consider increasing max_worker_processes to at least %d.",
						  num_dbs + 1);
		disconnect_database(conn, true);
	}
}

/*
 * Create the subscriptions, adjust the initial location for logical
 * replication and enable the subscriptions. That's the last step for logical
 * repliation setup.
 */
static void
setup_subscriber(struct LogicalRepInfo *dbinfo, const char *consistent_lsn)
{
	for (int i = 0; i < num_dbs; i++)
	{
		PGconn	   *conn;

		/* Connect to subscriber. */
		conn = connect_database(dbinfo[i].subconninfo, true);

		/*
		 * Since the publication was created before the consistent LSN, it is
		 * available on the subscriber when the physical replica is promoted.
		 * Remove publications from the subscriber because it has no use.
		 */
		drop_publication(conn, &dbinfo[i]);

		create_subscription(conn, &dbinfo[i]);

		/* Set the replication progress to the correct LSN */
		set_replication_progress(conn, &dbinfo[i], consistent_lsn);

		/* Enable subscription */
		enable_subscription(conn, &dbinfo[i]);

		disconnect_database(conn, false);
	}
}

/*
 * Create a logical replication slot and returns a LSN.
 *
 * CreateReplicationSlot() is not used because it does not provide the one-row
 * result set that contains the LSN.
 */
static char *
create_logical_replication_slot(PGconn *conn, struct LogicalRepInfo *dbinfo,
								bool temporary)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res = NULL;
	char		slot_name[NAMEDATALEN];
	char	   *lsn = NULL;

	Assert(conn != NULL);

	/* This temporary replication slot is only used for catchup purposes */
	if (temporary)
	{
		snprintf(slot_name, NAMEDATALEN, "pg_createsubscriber_%d_startpoint",
				 (int) getpid());
	}
	else
		snprintf(slot_name, NAMEDATALEN, "%s", dbinfo->subname);

	pg_log_info("creating the replication slot \"%s\" on database \"%s\"",
				slot_name, dbinfo->dbname);

	appendPQExpBuffer(str,
					  "SELECT lsn FROM pg_catalog.pg_create_logical_replication_slot('%s', '%s', %s, false, false)",
					  slot_name, "pgoutput", temporary ? "true" : "false");

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not create replication slot \"%s\" on database \"%s\": %s",
						 slot_name, dbinfo->dbname,
						 PQresultErrorMessage(res));
			return NULL;
		}

		lsn = pg_strdup(PQgetvalue(res, 0, 0));
		PQclear(res);
	}

	/* Cleanup if there is any failure */
	if (!temporary)
		dbinfo->made_replslot = true;

	destroyPQExpBuffer(str);

	return lsn;
}

static void
drop_replication_slot(PGconn *conn, struct LogicalRepInfo *dbinfo,
					  const char *slot_name)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("dropping the replication slot \"%s\" on database \"%s\"",
				slot_name, dbinfo->dbname);

	appendPQExpBuffer(str, "SELECT pg_catalog.pg_drop_replication_slot('%s')", slot_name);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
			pg_log_error("could not drop replication slot \"%s\" on database \"%s\": %s",
						 slot_name, dbinfo->dbname, PQresultErrorMessage(res));

		PQclear(res);
	}

	destroyPQExpBuffer(str);
}

/*
 * Create a directory to store any log information. Adjust the permissions.
 * Return a file name (full path) that's used by the standby server when it
 * starts the transformation.
 */
static char *
setup_server_logfile(const char *datadir)
{
	char		timebuf[128];
	struct timeval time;
	time_t		tt;
	int			len;
	char	   *base_dir;
	char	   *filename;

	base_dir = (char *) pg_malloc0(MAXPGPATH);
	len = snprintf(base_dir, MAXPGPATH, "%s/%s", datadir, BASE_OUTPUT_DIR);
	if (len >= MAXPGPATH)
		pg_fatal("directory path for subscriber is too long");

	if (!GetDataDirectoryCreatePerm(datadir))
		pg_fatal("could not read permissions of directory \"%s\": %m",
				 datadir);

	if (mkdir(base_dir, pg_dir_create_mode) < 0 && errno != EEXIST)
		pg_fatal("could not create directory \"%s\": %m", base_dir);

	/* Append timestamp with ISO 8601 format */
	gettimeofday(&time, NULL);
	tt = (time_t) time.tv_sec;
	strftime(timebuf, sizeof(timebuf), "%Y%m%dT%H%M%S", localtime(&tt));
	snprintf(timebuf + strlen(timebuf), sizeof(timebuf) - strlen(timebuf),
			 ".%03d", (int) (time.tv_usec / 1000));

	filename = (char *) pg_malloc0(MAXPGPATH);
	len = snprintf(filename, MAXPGPATH, "%s/server_start_%s.log", base_dir, timebuf);
	pg_log_debug("log file is: %s", filename);
	if (len >= MAXPGPATH)
		pg_fatal("log file path is too long");

	return filename;
}

/*
 * Reports a suitable message if pg_ctl fails.
 */
static void
pg_ctl_status(const char *pg_ctl_cmd, int rc)
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
			pg_log_error("pg_ctl was terminated by exception 0x%X",
						 WTERMSIG(rc));
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
}

static void
start_standby_server(struct CreateSubscriberOptions *opt, const char *pg_ctl_path,
					 const char *logfile)
{
	char	   *pg_ctl_cmd;
	char		socket_string[MAXPGPATH + 200];
	int			rc;

	socket_string[0] = '\0';

#if !defined(WIN32)
	/*
	 * An empty listen_addresses list means the server does not listen on any
	 * IP interfaces; only Unix-domain sockets can be used to connect to the
	 * server. Prevent external connections to minimize the chance of failure.
	 */
	strcat(socket_string,
			" -c listen_addresses='' -c unix_socket_permissions=0700");

	if (opt->socket_dir)
		snprintf(socket_string + strlen(socket_string),
				 sizeof(socket_string) - strlen(socket_string),
				 " -c unix_socket_directories='%s'",
				 opt->socket_dir);
#endif

	pg_ctl_cmd = psprintf("\"%s\" start -D \"%s\" -s -l \"%s\" -o \"-p %u%s\"",
						  pg_ctl_path, opt->subscriber_dir, logfile,
						  opt->sub_port, socket_string);
	pg_log_debug("pg_ctl command is: %s", pg_ctl_cmd);
	rc = system(pg_ctl_cmd);
	pg_ctl_status(pg_ctl_cmd, rc);
	pg_log_info("server was started");
}

static void
stop_standby_server(const char *pg_ctl_path, const char *datadir)
{
	char	   *pg_ctl_cmd;
	int			rc;

	pg_ctl_cmd = psprintf("\"%s\" stop -D \"%s\" -s", pg_ctl_path,
						  datadir);
	pg_log_debug("pg_ctl command is: %s", pg_ctl_cmd);
	rc = system(pg_ctl_cmd);
	pg_ctl_status(pg_ctl_cmd, rc);
	pg_log_info("server was stopped");
}

/*
 * Returns after the server finishes the recovery process.
 *
 * If recovery_timeout option is set, terminate abnormally without finishing
 * the recovery process. By default, it waits forever.
 */
static void
wait_for_end_recovery(const char *conninfo, const char *pg_ctl_path,
					  struct CreateSubscriberOptions *opt)
{
	PGconn	   *conn;
	int			status = POSTMASTER_STILL_STARTING;
	int			timer = 0;
	int			count = 0;		/* number of consecutive connection attempts */

#define NUM_CONN_ATTEMPTS	5

	pg_log_info("waiting the target server to reach the consistent state");

	conn = connect_database(conninfo, true);

	for (;;)
	{
		PGresult	*res;
		bool in_recovery = server_is_in_recovery(conn);

		/*
		 * Does the recovery process finish? In dry run mode, there is no
		 * recovery mode. Bail out as the recovery process has ended.
		 */
		if (!in_recovery || dry_run)
		{
			status = POSTMASTER_READY;
			recovery_ended = true;
			break;
		}

		/*
		 * If it is still in recovery, make sure the target server is connected
		 * to the primary so it can receive the required WAL to finish the
		 * recovery process. If it is disconnected try NUM_CONN_ATTEMPTS in a
		 * row and bail out if not succeed.
		 */
		res = PQexec(conn,
						"SELECT 1 FROM pg_catalog.pg_stat_wal_receiver");
		if (PQntuples(res) == 0)
		{
			if (++count > NUM_CONN_ATTEMPTS)
			{
				stop_standby_server(pg_ctl_path, opt->subscriber_dir);
				pg_log_error("standby server disconnected from the primary");
				break;
			}
		}
		else
			count = 0;		/* reset counter if it connects again */

		PQclear(res);

		/* Bail out after recovery_timeout seconds if this option is set */
		if (opt->recovery_timeout > 0 && timer >= opt->recovery_timeout)
		{
			stop_standby_server(pg_ctl_path, opt->subscriber_dir);
			pg_log_error("recovery timed out");
			disconnect_database(conn, true);
		}

		/* Keep waiting */
		pg_usleep(WAIT_INTERVAL * USEC_PER_SEC);

		timer += WAIT_INTERVAL;
	}

	disconnect_database(conn, false);

	if (status == POSTMASTER_STILL_STARTING)
		pg_fatal("server did not end recovery");

	pg_log_info("target server reached the consistent state");
	pg_log_info_hint("If pg_createsubscriber fails after this point, "
			"you must recreate the physical replica before continuing.");
}

/*
 * Create a publication that includes all tables in the database.
 */
static void
create_publication(PGconn *conn, struct LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	/* Check if the publication already exists */
	appendPQExpBuffer(str,
					  "SELECT 1 FROM pg_catalog.pg_publication "
					  "WHERE pubname = '%s'",
					  dbinfo->pubname);
	res = PQexec(conn, str->data);
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain publication information: %s",
				 PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}

	if (PQntuples(res) == 1)
	{
		/*
		 * Unfortunately, if it reaches this code path, it will always
		 * fail (unless you decide to change the existing publication
		 * name). That's bad but it is very unlikely that the user will
		 * choose a name with pg_createsubscriber_ prefix followed by the
		 * exact database oid.
		 */
		pg_log_error("publication \"%s\" already exists", dbinfo->pubname);
		pg_log_error_hint("Consider renaming this publication before continuing.");
		disconnect_database(conn, true);
	}

	PQclear(res);
	resetPQExpBuffer(str);

	pg_log_info("creating publication \"%s\" on database \"%s\"",
				dbinfo->pubname, dbinfo->dbname);

	appendPQExpBuffer(str, "CREATE PUBLICATION %s FOR ALL TABLES",
					  dbinfo->pubname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			pg_log_error("could not create publication \"%s\" on database \"%s\": %s",
					 dbinfo->pubname, dbinfo->dbname, PQresultErrorMessage(res));
			disconnect_database(conn, true);
		}
		PQclear(res);
	}

	/* for cleanup purposes */
	dbinfo->made_publication = true;

	destroyPQExpBuffer(str);
}

/*
 * Remove publication if it couldn't finish all steps.
 */
static void
drop_publication(PGconn *conn, struct LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("dropping publication \"%s\" on database \"%s\"",
				dbinfo->pubname, dbinfo->dbname);

	appendPQExpBuffer(str, "DROP PUBLICATION %s", dbinfo->pubname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			pg_log_error("could not drop publication \"%s\" on database \"%s\": %s",
						 dbinfo->pubname, dbinfo->dbname, PQresultErrorMessage(res));
			disconnect_database(conn, true);
		}
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
create_subscription(PGconn *conn, struct LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("creating subscription \"%s\" on database \"%s\"",
				dbinfo->subname, dbinfo->dbname);

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
					 dbinfo->subname, dbinfo->dbname, PQresultErrorMessage(res));
			disconnect_database(conn, true);
		}
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
set_replication_progress(PGconn *conn, struct LogicalRepInfo *dbinfo, const char *lsn)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;
	Oid			suboid;
	char		originname[NAMEDATALEN];
	char		lsnstr[17 + 1]; /* MAXPG_LSNLEN = 17 */

	Assert(conn != NULL);

	appendPQExpBuffer(str,
					  "SELECT oid FROM pg_catalog.pg_subscription "
					  "WHERE subname = '%s'",
					  dbinfo->subname);

	res = PQexec(conn, str->data);
	if (PQresultStatus(res) != PGRES_TUPLES_OK)
	{
		pg_log_error("could not obtain subscription OID: %s",
				 PQresultErrorMessage(res));
		disconnect_database(conn, true);
	}

	if (PQntuples(res) != 1 && !dry_run)
	{
		pg_log_error("could not obtain subscription OID: got %d rows, expected %d rows",
				 PQntuples(res), 1);
		disconnect_database(conn, true);
	}

	if (dry_run)
	{
		suboid = InvalidOid;
		snprintf(lsnstr, sizeof(lsnstr), "%X/%X",
				 LSN_FORMAT_ARGS((XLogRecPtr) InvalidXLogRecPtr));
	}
	else
	{
		suboid = strtoul(PQgetvalue(res, 0, 0), NULL, 10);
		snprintf(lsnstr, sizeof(lsnstr), "%s", lsn);
	}

	PQclear(res);

	/*
	 * The origin name is defined as pg_%u. %u is the subscription OID. See
	 * ApplyWorkerMain().
	 */
	snprintf(originname, sizeof(originname), "pg_%u", suboid);

	pg_log_info("setting the replication progress (node name \"%s\" ; LSN %s) on database \"%s\"",
				originname, lsnstr, dbinfo->dbname);

	resetPQExpBuffer(str);
	appendPQExpBuffer(str,
					  "SELECT pg_catalog.pg_replication_origin_advance('%s', '%s')",
					  originname, lsnstr);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_TUPLES_OK)
		{
			pg_log_error("could not set replication progress for the subscription \"%s\": %s",
					 dbinfo->subname, PQresultErrorMessage(res));
			disconnect_database(conn, true);
		}
		PQclear(res);
	}

	destroyPQExpBuffer(str);
}

/*
 * Enables the subscription.
 *
 * The subscription was created in a previous step but it was disabled. After
 * adjusting the initial logical replication location, enable the subscription.
 */
static void
enable_subscription(PGconn *conn, struct LogicalRepInfo *dbinfo)
{
	PQExpBuffer str = createPQExpBuffer();
	PGresult   *res;

	Assert(conn != NULL);

	pg_log_info("enabling subscription \"%s\" on database \"%s\"",
				dbinfo->subname, dbinfo->dbname);

	appendPQExpBuffer(str, "ALTER SUBSCRIPTION %s ENABLE", dbinfo->subname);

	pg_log_debug("command is: %s", str->data);

	if (!dry_run)
	{
		res = PQexec(conn, str->data);
		if (PQresultStatus(res) != PGRES_COMMAND_OK)
		{
			pg_log_error("could not enable subscription \"%s\": %s",
					 dbinfo->subname, PQresultErrorMessage(res));
			disconnect_database(conn, true);
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
		{"database", required_argument, NULL, 'd'},
		{"pgdata", required_argument, NULL, 'D'},
		{"dry-run", no_argument, NULL, 'n'},
		{"subscriber-port", required_argument, NULL, 'p'},
		{"publisher-server", required_argument, NULL, 'P'},
		{"retain", no_argument, NULL, 'r'},
		{"socket-directory", required_argument, NULL, 's'},
		{"recovery-timeout", required_argument, NULL, 't'},
		{"subscriber-username", required_argument, NULL, 'U'},
		{"verbose", no_argument, NULL, 'v'},
		{"version", no_argument, NULL, 'V'},
		{"help", no_argument, NULL, '?'},
		{NULL, 0, NULL, 0}
	};

	struct CreateSubscriberOptions opt = {0};

	int			c;
	int			option_index;

	char	   *pg_ctl_path = NULL;
	char	   *pg_resetwal_path = NULL;

	char	   *server_start_log;

	char	   *pub_base_conninfo = NULL;
	char	   *sub_base_conninfo = NULL;
	char	   *dbname_conninfo = NULL;

	uint64		pub_sysid;
	uint64		sub_sysid;
	struct stat statbuf;

	PGconn	   *conn;
	char	   *consistent_lsn;

	PQExpBuffer sub_conninfo_str = createPQExpBuffer();
	PQExpBuffer recoveryconfcontents = NULL;

	char		pidfile[MAXPGPATH];

	pg_logging_init(argv[0]);
	pg_logging_set_level(PG_LOG_WARNING);
	progname = get_progname(argv[0]);
	set_pglocale_pgservice(argv[0], PG_TEXTDOMAIN("pg_createsubscriber"));

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
			puts("pg_createsubscriber (PostgreSQL) " PG_VERSION);
			exit(0);
		}
	}

	/* Default settings */
	opt.subscriber_dir = NULL;
	opt.pub_conninfo_str = NULL;
	opt.socket_dir = NULL;
	opt.sub_port = DEFAULT_SUB_PORT;
	opt.sub_username = NULL;
	opt.database_names = (SimpleStringList)
	{
		NULL, NULL
	};
	opt.retain = false;
	opt.recovery_timeout = 0;

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

	get_restricted_token();

	while ((c = getopt_long(argc, argv, "d:D:nP:rS:t:v",
							long_options, &option_index)) != -1)
	{
		switch (c)
		{
			case 'd':
				/* Ignore duplicated database names */
				if (!simple_string_list_member(&opt.database_names, optarg))
				{
					simple_string_list_append(&opt.database_names, optarg);
					num_dbs++;
				}
				break;
			case 'D':
				opt.subscriber_dir = pg_strdup(optarg);
				canonicalize_path(opt.subscriber_dir);
				break;
			case 'n':
				dry_run = true;
				break;
			case 'p':
				if ((opt.sub_port = atoi(optarg)) <= 0)
					pg_fatal("invalid subscriber port number");
				break;
			case 'P':
				opt.pub_conninfo_str = pg_strdup(optarg);
				break;
			case 'r':
				opt.retain = true;
				break;
			case 's':
				opt.socket_dir = pg_strdup(optarg);
				break;
			case 't':
				opt.recovery_timeout = atoi(optarg);
				break;
			case 'U':
				opt.sub_username = pg_strdup(optarg);
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
	if (opt.subscriber_dir == NULL)
	{
		pg_log_error("no subscriber data directory specified");
		pg_log_error_hint("Try \"%s --help\" for more information.", progname);
		exit(1);
	}

	/*
	 * If socket directory is not provided, use the current directory.
	 */
	if (opt.socket_dir == NULL)
	{
		char	cwd[MAXPGPATH];

		if (!getcwd(cwd, MAXPGPATH))
			pg_fatal("could not determine current directory");
		opt.socket_dir = pg_strdup(cwd);
		canonicalize_path(opt.socket_dir);
	}

	/*
	 *
	 * If subscriber username is not provided, check if the environment
	 * variable sets it. If not, obtain the operating system name of the user
	 * running it.
	 */
	if (opt.sub_username == NULL)
	{
		char		*errstr = NULL;

		if (getenv("PGUSER"))
		{
			opt.sub_username = getenv("PGUSER");
		}
		else
		{
			opt.sub_username = get_user_name(&errstr);
			if (errstr)
				pg_fatal("%s", errstr);
		}
	}

	/*
	 * Parse connection string. Build a base connection string that might be
	 * reused by multiple databases.
	 */
	if (opt.pub_conninfo_str == NULL)
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
	pg_log_info("validating connection string on publisher");
	pub_base_conninfo = get_base_conninfo(opt.pub_conninfo_str,
										  &dbname_conninfo);
	if (pub_base_conninfo == NULL)
		exit(1);

	pg_log_info("validating connection string on subscriber");
	appendPQExpBuffer(sub_conninfo_str, "host=%s port=%u user=%s fallback_application_name=%s",
					opt.socket_dir, opt.sub_port, opt.sub_username, progname);
	sub_base_conninfo = get_base_conninfo(sub_conninfo_str->data, NULL);
	if (sub_base_conninfo == NULL)
		exit(1);

	if (opt.database_names.head == NULL)
	{
		pg_log_info("no database was specified");

		/*
		 * If --database option is not provided, try to obtain the dbname from
		 * the publisher conninfo. If dbname parameter is not available, error
		 * out.
		 */
		if (dbname_conninfo)
		{
			simple_string_list_append(&opt.database_names, dbname_conninfo);
			num_dbs++;

			pg_log_info("database \"%s\" was extracted from the publisher connection string",
						dbname_conninfo);
		}
		else
		{
			pg_log_error("no database name specified");
			pg_log_error_hint("Try \"%s --help\" for more information.",
							  progname);
			exit(1);
		}
	}

	/* Get the absolute path of pg_ctl and pg_resetwal on the subscriber */
	pg_ctl_path = get_exec_path(argv[0], "pg_ctl");
	pg_resetwal_path = get_exec_path(argv[0], "pg_resetwal");

	/* Rudimentary check for a data directory */
	check_data_directory(opt.subscriber_dir);

	/* Store database information for publisher and subscriber */
	dbinfo = store_pub_sub_info(opt.database_names, pub_base_conninfo,
								sub_base_conninfo);

	/* Register a function to clean up objects in case of failure */
	atexit(cleanup_objects_atexit);

	/*
	 * Check if the subscriber data directory has the same system identifier
	 * than the publisher data directory.
	 */
	pub_sysid = get_primary_sysid(dbinfo[0].pubconninfo);
	sub_sysid = get_standby_sysid(opt.subscriber_dir);
	if (pub_sysid != sub_sysid)
		pg_fatal("subscriber data directory is not a copy of the source database cluster");

	/* Create the output directory to store any data generated by this tool */
	server_start_log = setup_server_logfile(opt.subscriber_dir);

	/* Subscriber PID file */
	snprintf(pidfile, MAXPGPATH, "%s/postmaster.pid", opt.subscriber_dir);

	/*
	 * The standby server must be running. That's because some checks will be
	 * done (is it ready for a logical replication setup?). After that, stop
	 * the subscriber in preparation to modify some recovery parameters that
	 * require a restart.
	 */
	if (stat(pidfile, &statbuf) == 0)
	{
		/* Check if the standby server is ready for logical replication */
		check_subscriber(dbinfo);

		/*
		 * Check if the primary server is ready for logical replication. This
		 * routine checks if a replication slot is in use on primary so it
		 * relies on check_subscriber() to obtain the primary_slot_name.
		 * That's why it is called after it.
		 */
		check_publisher(dbinfo);

		/*
		 * Create the required objects for each database on publisher. This
		 * step is here mainly because if we stop the standby we cannot verify
		 * if the primary slot is in use. We could use an extra connection for
		 * it but it doesn't seem worth.
		 */
		setup_publisher(dbinfo);

		/* Stop the standby server */
		pg_log_info("standby is up and running");
		pg_log_info("stopping the server to start the transformation steps");
		if (!dry_run)
			stop_standby_server(pg_ctl_path, opt.subscriber_dir);
	}
	else
	{
		pg_log_error("standby is not running");
		pg_log_error_hint("Start the standby and try again.");
		exit(1);
	}

	/*
	 * Create a temporary logical replication slot to get a consistent LSN.
	 *
	 * This consistent LSN will be used later to advanced the recently created
	 * replication slots. It is ok to use a temporary replication slot here
	 * because it will have a short lifetime and it is only used as a mark to
	 * start the logical replication.
	 *
	 * XXX we should probably use the last created replication slot to get a
	 * consistent LSN but it should be changed after adding pg_basebackup
	 * support.
	 */
	conn = connect_database(dbinfo[0].pubconninfo, true);
	consistent_lsn = create_logical_replication_slot(conn, &dbinfo[0], true);

	/*
	 * Write recovery parameters.
	 *
	 * Despite of the recovery parameters will be written to the subscriber,
	 * use a publisher connection for the following recovery functions. The
	 * connection is only used to check the current server version (physical
	 * replica, same server version). The subscriber is not running yet. In
	 * dry run mode, the recovery parameters *won't* be written. An invalid
	 * LSN is used for printing purposes. Additional recovery parameters are
	 * added here. It avoids unexpected behavior such as end of recovery as
	 * soon as a consistent state is reached (recovery_target) and failure due
	 * to multiple recovery targets (name, time, xid, LSN).
	 */
	recoveryconfcontents = GenerateRecoveryConfig(conn, NULL);
	appendPQExpBuffer(recoveryconfcontents, "recovery_target = ''\n");
	appendPQExpBuffer(recoveryconfcontents,
					  "recovery_target_timeline = 'latest'\n");
	appendPQExpBuffer(recoveryconfcontents,
					  "recovery_target_inclusive = true\n");
	appendPQExpBuffer(recoveryconfcontents,
					  "recovery_target_action = promote\n");
	appendPQExpBuffer(recoveryconfcontents, "recovery_target_name = ''\n");
	appendPQExpBuffer(recoveryconfcontents, "recovery_target_time = ''\n");
	appendPQExpBuffer(recoveryconfcontents, "recovery_target_xid = ''\n");

	if (dry_run)
	{
		appendPQExpBuffer(recoveryconfcontents, "# dry run mode");
		appendPQExpBuffer(recoveryconfcontents,
						  "recovery_target_lsn = '%X/%X'\n",
						  LSN_FORMAT_ARGS((XLogRecPtr) InvalidXLogRecPtr));
	}
	else
	{
		appendPQExpBuffer(recoveryconfcontents, "recovery_target_lsn = '%s'\n",
						  consistent_lsn);
		WriteRecoveryConfig(conn, opt.subscriber_dir, recoveryconfcontents);
	}
	disconnect_database(conn, false);

	pg_log_debug("recovery parameters:\n%s", recoveryconfcontents->data);

	/* Start subscriber and wait until accepting connections */
	pg_log_info("starting the subscriber");
	if (!dry_run)
		start_standby_server(&opt, pg_ctl_path, server_start_log);

	/* Waiting the subscriber to be promoted */
	wait_for_end_recovery(dbinfo[0].subconninfo, pg_ctl_path, &opt);

	/*
	 * Create the subscription for each database on subscriber. It does not
	 * enable it immediately because it needs to adjust the logical
	 * replication start point to the LSN reported by consistent_lsn (see
	 * set_replication_progress). It also cleans up publications created by
	 * this tool and replication to the standby.
	 */
	setup_subscriber(dbinfo, consistent_lsn);

	/*
	 * If the primary_slot_name exists on primary, drop it.
	 *
	 * XXX we might not fail here. Instead, we provide a warning so the user
	 * eventually drops this replication slot later.
	 */
	if (primary_slot_name != NULL)
	{
		conn = connect_database(dbinfo[0].pubconninfo, false);
		if (conn != NULL)
		{
			drop_replication_slot(conn, &dbinfo[0], primary_slot_name);
			disconnect_database(conn, false);
		}
		else
		{
			pg_log_warning("could not drop replication slot \"%s\" on primary",
						   primary_slot_name);
			pg_log_warning_hint("Drop this replication slot soon to avoid retention of WAL files.");
		}
	}

	/* Stop the subscriber */
	pg_log_info("stopping the subscriber");
	if (!dry_run)
		stop_standby_server(pg_ctl_path, opt.subscriber_dir);

	/* Change system identifier from subscriber */
	modify_subscriber_sysid(pg_resetwal_path, &opt);

	/*
	 * The log file is kept if retain option is specified or this tool does
	 * not run successfully. Otherwise, log file is removed.
	 */
	if (!opt.retain)
		unlink(server_start_log);

	success = true;

	pg_log_info("Done!");

	return 0;
}
