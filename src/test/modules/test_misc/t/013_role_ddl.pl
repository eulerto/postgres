
# Copyright (c) 2026, PostgreSQL Global Development Group

# Tests for pg_get_role_ddl()

use strict;
use warnings FATAL => 'all';
use PostgreSQL::Test::Cluster;
use PostgreSQL::Test::Utils;
use Test::More;

my $node = PostgreSQL::Test::Cluster->new('main');
$node->init;
$node->start;

# Consistent test results
$node->safe_psql('postgres', "SET timezone TO 'UTC'");

# Create test database for database-specific configuration test
$node->safe_psql('postgres', 'CREATE DATABASE regression_role_ddl_test');

# Basic role
$node->safe_psql('postgres', 'CREATE ROLE regress_role_ddl_test1');
my $result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_role_ddl('regress_role_ddl_test1')");
is( $result,
	'CREATE ROLE regress_role_ddl_test1 NOSUPERUSER INHERIT NOCREATEROLE NOCREATEDB NOLOGIN NOREPLICATION NOBYPASSRLS;',
	'basic role DDL');

# Role with LOGIN
$node->safe_psql('postgres', 'CREATE ROLE regress_role_ddl_test2 LOGIN');
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_role_ddl('regress_role_ddl_test2')");
is( $result,
	'CREATE ROLE regress_role_ddl_test2 NOSUPERUSER INHERIT NOCREATEROLE NOCREATEDB LOGIN NOREPLICATION NOBYPASSRLS;',
	'role with LOGIN');

# Role with multiple privileges
$node->safe_psql(
	'postgres', q{
CREATE ROLE regress_role_ddl_test3
  LOGIN
  SUPERUSER
  CREATEDB
  CREATEROLE
  CONNECTION LIMIT 5
  VALID UNTIL '2030-12-31 23:59:59+00';
});
$result = $node->safe_psql(
	'postgres', q{
SET timezone TO 'UTC';
SELECT * FROM pg_get_role_ddl('regress_role_ddl_test3');
});
is( $result,
	"CREATE ROLE regress_role_ddl_test3 SUPERUSER INHERIT CREATEROLE CREATEDB LOGIN NOREPLICATION NOBYPASSRLS CONNECTION LIMIT 5 VALID UNTIL '2030-12-31 23:59:59+00';",
	'role with multiple privileges');

# Role with configuration parameters
$node->safe_psql(
	'postgres', q{
CREATE ROLE regress_role_ddl_test4;
ALTER ROLE regress_role_ddl_test4 SET work_mem TO '256MB';
ALTER ROLE regress_role_ddl_test4 SET search_path TO myschema, public;
});
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_role_ddl('regress_role_ddl_test4')");
is( $result,
	"CREATE ROLE regress_role_ddl_test4 NOSUPERUSER INHERIT NOCREATEROLE NOCREATEDB NOLOGIN NOREPLICATION NOBYPASSRLS;
ALTER ROLE regress_role_ddl_test4 SET work_mem TO '256MB';
ALTER ROLE regress_role_ddl_test4 SET search_path TO 'myschema', 'public';",
	'role with configuration parameters');

# Role with database-specific configuration
$node->safe_psql(
	'postgres', q{
CREATE ROLE regress_role_ddl_test5;
ALTER ROLE regress_role_ddl_test5 IN DATABASE regression_role_ddl_test SET work_mem TO '128MB';
});
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_role_ddl('regress_role_ddl_test5')");
is( $result,
	"CREATE ROLE regress_role_ddl_test5 NOSUPERUSER INHERIT NOCREATEROLE NOCREATEDB NOLOGIN NOREPLICATION NOBYPASSRLS;
ALTER ROLE regress_role_ddl_test5 IN DATABASE regression_role_ddl_test SET work_mem TO '128MB';",
	'role with database-specific configuration');

# Role with special characters (requires quoting)
$node->safe_psql('postgres', 'CREATE ROLE "regress_role-with-dash"');
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_role_ddl('regress_role-with-dash')");
is( $result,
	'CREATE ROLE "regress_role-with-dash" NOSUPERUSER INHERIT NOCREATEROLE NOCREATEDB NOLOGIN NOREPLICATION NOBYPASSRLS;',
	'role with special characters requiring quoting');

# Pretty-printed output
$result = $node->safe_psql(
	'postgres', q{
SET timezone TO 'UTC';
SELECT * FROM pg_get_role_ddl('regress_role_ddl_test3', 'pretty', 'true');
});
is( $result,
	"CREATE ROLE regress_role_ddl_test3
    SUPERUSER
    INHERIT
    CREATEROLE
    CREATEDB
    LOGIN
    NOREPLICATION
    NOBYPASSRLS
    CONNECTION LIMIT 5
    VALID UNTIL '2030-12-31 23:59:59+00';",
	'role DDL pretty-printed');

# Role with memberships
$node->safe_psql(
	'postgres', q{
CREATE ROLE regress_role_ddl_grantor CREATEROLE;
CREATE ROLE regress_role_ddl_group1;
CREATE ROLE regress_role_ddl_group2;
CREATE ROLE regress_role_ddl_member;
GRANT regress_role_ddl_group1 TO regress_role_ddl_grantor WITH ADMIN TRUE;
GRANT regress_role_ddl_group2 TO regress_role_ddl_grantor WITH ADMIN TRUE;
SET ROLE regress_role_ddl_grantor;
GRANT regress_role_ddl_group1 TO regress_role_ddl_member WITH INHERIT TRUE, SET FALSE;
GRANT regress_role_ddl_group2 TO regress_role_ddl_member WITH ADMIN TRUE;
RESET ROLE;
});
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_role_ddl('regress_role_ddl_member')");
is( $result,
	'CREATE ROLE regress_role_ddl_member NOSUPERUSER INHERIT NOCREATEROLE NOCREATEDB NOLOGIN NOREPLICATION NOBYPASSRLS;
GRANT regress_role_ddl_group1 TO regress_role_ddl_member WITH ADMIN FALSE, INHERIT TRUE, SET FALSE GRANTED BY regress_role_ddl_grantor;
GRANT regress_role_ddl_group2 TO regress_role_ddl_member WITH ADMIN TRUE, INHERIT TRUE, SET TRUE GRANTED BY regress_role_ddl_grantor;',
	'role with memberships');

# Role with memberships suppressed
$result = $node->safe_psql('postgres',
	"SELECT * FROM pg_get_role_ddl('regress_role_ddl_member', 'memberships', 'false')"
);
is( $result,
	'CREATE ROLE regress_role_ddl_member NOSUPERUSER INHERIT NOCREATEROLE NOCREATEDB NOLOGIN NOREPLICATION NOBYPASSRLS;',
	'role with memberships suppressed');

# Non-existent role (should error)
my ($ret, $stdout, $stderr) =
  $node->psql('postgres', "SELECT * FROM pg_get_role_ddl(9999999::oid)");
isnt($ret, 0, 'error for non-existent role');
like(
	$stderr,
	qr/role with OID 9999999 does not exist/,
	'error message for non-existent role');

# NULL input returns no rows
$result = $node->safe_psql('postgres', "SELECT * FROM pg_get_role_ddl(NULL)");
is($result, '', 'NULL input returns no rows');

# Permission check: revoke SELECT on pg_authid
$node->safe_psql(
	'postgres', q{
CREATE ROLE regress_role_ddl_noaccess;
REVOKE SELECT ON pg_authid FROM PUBLIC;
});
($ret, $stdout, $stderr) = $node->psql('postgres',
	"SET ROLE regress_role_ddl_noaccess; SELECT * FROM pg_get_role_ddl('regress_role_ddl_test1')"
);
isnt($ret, 0, 'permission denied without SELECT on pg_authid');
like(
	$stderr,
	qr/permission denied for role regress_role_ddl_test1/,
	'permission error message for role DDL');

# Cleanup
$node->safe_psql(
	'postgres', q{
GRANT SELECT ON pg_authid TO PUBLIC;
DROP ROLE regress_role_ddl_noaccess;
DROP ROLE regress_role_ddl_test1;
DROP ROLE regress_role_ddl_test2;
DROP ROLE regress_role_ddl_test3;
DROP ROLE regress_role_ddl_test4;
DROP ROLE regress_role_ddl_test5;
DROP ROLE "regress_role-with-dash";
SET ROLE regress_role_ddl_grantor;
REVOKE regress_role_ddl_group1 FROM regress_role_ddl_member;
REVOKE regress_role_ddl_group2 FROM regress_role_ddl_member;
RESET ROLE;
DROP ROLE regress_role_ddl_member;
DROP ROLE regress_role_ddl_group1;
DROP ROLE regress_role_ddl_group2;
DROP ROLE regress_role_ddl_grantor;
DROP DATABASE regression_role_ddl_test;
});

$node->stop;

done_testing();
