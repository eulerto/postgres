
# Copyright (c) 2026, PostgreSQL Global Development Group

# Tests for pg_get_tablespace_ddl()

use strict;
use warnings FATAL => 'all';
use PostgreSQL::Test::Cluster;
use PostgreSQL::Test::Utils;
use Test::More;

my $node = PostgreSQL::Test::Cluster->new('main');
$node->init;
$node->start;

$node->safe_psql(
	'postgres', q{
SET allow_in_place_tablespaces = true;
CREATE ROLE regress_tblspc_ddl_user;
});

# Error: non-existent tablespace by name
my ($ret, $stdout, $stderr) = $node->psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl('regress_nonexistent_tblsp')");
isnt($ret, 0, 'error for non-existent tablespace by name');
like(
	$stderr,
	qr/tablespace "regress_nonexistent_tblsp" does not exist/,
	'error message for non-existent tablespace by name');

# Error: non-existent tablespace by OID
($ret, $stdout, $stderr) =
  $node->psql('postgres', "SELECT * FROM pg_get_tablespace_ddl(0::oid)");
isnt($ret, 0, 'error for non-existent tablespace by OID');
like(
	$stderr,
	qr/tablespace with OID 0 does not exist/,
	'error message for non-existent tablespace by OID');

# NULL input returns no rows (name variant)
my $result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl(NULL::name)");
is($result, '', 'NULL name input returns no rows');

# NULL input returns no rows (OID variant)
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl(NULL::oid)");
is($result, '', 'NULL OID input returns no rows');

# Tablespace name requiring quoting
$node->safe_psql(
	'postgres', q{
SET allow_in_place_tablespaces = true;
CREATE TABLESPACE "regress_ tblsp" OWNER regress_tblspc_ddl_user LOCATION '';
});
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl('regress_ tblsp')");
is( $result,
	q{CREATE TABLESPACE "regress_ tblsp" OWNER regress_tblspc_ddl_user LOCATION '';},
	'tablespace name requiring quoting');
$node->safe_psql('postgres', 'DROP TABLESPACE "regress_ tblsp"');

# Tablespace with multiple options
$node->safe_psql(
	'postgres', q{
SET allow_in_place_tablespaces = true;
CREATE TABLESPACE regress_allopt_tblsp OWNER regress_tblspc_ddl_user LOCATION ''
  WITH (seq_page_cost = '1.5', random_page_cost = '1.1234567890',
        effective_io_concurrency = '17', maintenance_io_concurrency = '18');
});
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl('regress_allopt_tblsp')");
is( $result,
	"CREATE TABLESPACE regress_allopt_tblsp OWNER regress_tblspc_ddl_user LOCATION '';
ALTER TABLESPACE regress_allopt_tblsp SET (seq_page_cost='1.5', random_page_cost='1.1234567890', effective_io_concurrency='17', maintenance_io_concurrency='18');",
	'tablespace with multiple options');

# Pretty-printed output
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl('regress_allopt_tblsp', 'pretty', 'true')"
);
is( $result,
	"CREATE TABLESPACE regress_allopt_tblsp
    OWNER regress_tblspc_ddl_user
    LOCATION '';
ALTER TABLESPACE regress_allopt_tblsp SET (seq_page_cost='1.5', random_page_cost='1.1234567890', effective_io_concurrency='17', maintenance_io_concurrency='18');",
	'tablespace DDL pretty-printed');

# Tablespace with owner suppressed
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl('regress_allopt_tblsp', 'owner', 'false')"
);
is( $result,
	"CREATE TABLESPACE regress_allopt_tblsp LOCATION '';
ALTER TABLESPACE regress_allopt_tblsp SET (seq_page_cost='1.5', random_page_cost='1.1234567890', effective_io_concurrency='17', maintenance_io_concurrency='18');",
	'tablespace with owner suppressed');

$node->safe_psql('postgres', 'DROP TABLESPACE regress_allopt_tblsp');

# Test by OID
$node->safe_psql(
	'postgres', q{
SET allow_in_place_tablespaces = true;
CREATE TABLESPACE regress_oid_tblsp OWNER regress_tblspc_ddl_user LOCATION '';
});
my $tsid = $node->safe_psql('postgres',
	"SELECT oid FROM pg_tablespace WHERE spcname = 'regress_oid_tblsp'");
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_tablespace_ddl(${tsid}::oid)");
is( $result,
	q{CREATE TABLESPACE regress_oid_tblsp OWNER regress_tblspc_ddl_user LOCATION '';},
	'tablespace DDL by OID');
$node->safe_psql('postgres', 'DROP TABLESPACE regress_oid_tblsp');

# Permission check: revoke SELECT on pg_tablespace
$node->safe_psql(
	'postgres', q{
SET allow_in_place_tablespaces = true;
CREATE TABLESPACE regress_acl_tblsp OWNER regress_tblspc_ddl_user LOCATION '';
CREATE ROLE regress_tblspc_ddl_noaccess;
REVOKE SELECT ON pg_tablespace FROM PUBLIC;
});
($ret, $stdout, $stderr) = $node->psql('postgres',
	"SET ROLE regress_tblspc_ddl_noaccess; SELECT * FROM pg_get_tablespace_ddl('regress_acl_tblsp')"
);
isnt($ret, 0, 'permission denied without SELECT on pg_tablespace');
like(
	$stderr,
	qr/permission denied for tablespace regress_acl_tblsp/,
	'permission error message for tablespace DDL');

# Cleanup
$node->safe_psql(
	'postgres', q{
GRANT SELECT ON pg_tablespace TO PUBLIC;
DROP TABLESPACE regress_acl_tblsp;
DROP ROLE regress_tblspc_ddl_noaccess;
DROP ROLE regress_tblspc_ddl_user;
});

$node->stop;

done_testing();
