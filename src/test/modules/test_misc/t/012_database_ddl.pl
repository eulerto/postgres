
# Copyright (c) 2026, PostgreSQL Global Development Group

# Tests for pg_get_database_ddl()

use strict;
use warnings FATAL => 'all';
use PostgreSQL::Test::Cluster;
use PostgreSQL::Test::Utils;
use Test::More;

my $node = PostgreSQL::Test::Cluster->new('main');
$node->init;
$node->start;

# To produce stable test output, strip locale/collation details from the
# DDL output.
my $ddl_filter_func = q{
CREATE OR REPLACE FUNCTION ddl_filter(ddl_input TEXT)
RETURNS TEXT LANGUAGE sql AS $$
SELECT regexp_replace(
  regexp_replace(
    regexp_replace(
      regexp_replace(
        regexp_replace(
          ddl_input,
          '\s*\mLOCALE_PROVIDER\M\s*=\s*([''"]?[^''"\s]+[''"]?)', '', 'gi'),
        '\s*LC_COLLATE\s*=\s*([''"])[^''"]*\1', '', 'gi'),
      '\s*LC_CTYPE\s*=\s*([''"])[^''"]*\1', '', 'gi'),
    '\s*\S*LOCALE\S*\s*=?\s*([''"])[^''"]*\1', '', 'gi'),
  '\s*\S*COLLATION\S*\s*=?\s*([''"])[^''"]*\1', '', 'gi')
$$;
};

# Setup: create filter function, role, and test database
$node->safe_psql('postgres', $ddl_filter_func);
$node->safe_psql('postgres', 'CREATE ROLE regress_datdba');
$node->safe_psql(
	'postgres', q{
CREATE DATABASE regression_database_ddl
    ENCODING utf8 LC_COLLATE "C" LC_CTYPE "C" TEMPLATE template0
    OWNER regress_datdba;
ALTER DATABASE regression_database_ddl CONNECTION_LIMIT 123;
ALTER DATABASE regression_database_ddl SET random_page_cost = 2.0;
ALTER ROLE regress_datdba IN DATABASE regression_database_ddl SET random_page_cost = 1.1;
});

# Database doesn't exist
my ($ret, $stdout, $stderr) =
  $node->psql('postgres',
	"SELECT * FROM pg_get_database_ddl('regression_database')");
isnt($ret, 0, 'error for non-existent database');
like(
	$stderr,
	qr/database "regression_database" does not exist/,
	'error message for non-existent database');

# NULL value returns no rows
my $result =
  $node->safe_psql('postgres', "SELECT * FROM pg_get_database_ddl(NULL)");
is($result, '', 'NULL input returns no rows');

# Invalid option value
($ret, $stdout, $stderr) = $node->psql('postgres',
	"SELECT * FROM pg_get_database_ddl('regression_database_ddl', 'owner', 'invalid')"
);
isnt($ret, 0, 'error for invalid option value');
like(
	$stderr,
	qr/invalid value for boolean option "owner": invalid/,
	'error message for invalid option value');

# Duplicate option
($ret, $stdout, $stderr) = $node->psql('postgres',
	"SELECT * FROM pg_get_database_ddl('regression_database_ddl', 'owner', 'false', 'owner', 'true')"
);
isnt($ret, 0, 'error for duplicate option');
like(
	$stderr,
	qr/option "owner" is specified more than once/,
	'error message for duplicate option');

# Without options
$result = $node->safe_psql('postgres',
	"SELECT ddl_filter(pg_get_database_ddl) FROM pg_get_database_ddl('regression_database_ddl')"
);
is( $result,
	"CREATE DATABASE regression_database_ddl WITH TEMPLATE = template0 ENCODING = 'UTF8';
ALTER DATABASE regression_database_ddl OWNER TO regress_datdba;
ALTER DATABASE regression_database_ddl CONNECTION LIMIT = 123;
ALTER DATABASE regression_database_ddl SET random_page_cost TO '2.0';",
	'database DDL without options');

# With owner option
$result = $node->safe_psql('postgres',
	"SELECT ddl_filter(pg_get_database_ddl) FROM pg_get_database_ddl('regression_database_ddl', 'owner', 'true')"
);
is( $result,
	"CREATE DATABASE regression_database_ddl WITH TEMPLATE = template0 ENCODING = 'UTF8';
ALTER DATABASE regression_database_ddl OWNER TO regress_datdba;
ALTER DATABASE regression_database_ddl CONNECTION LIMIT = 123;
ALTER DATABASE regression_database_ddl SET random_page_cost TO '2.0';",
	'database DDL with owner option');

# Pretty-printed output
$result = $node->safe_psql('postgres',
	"SELECT ddl_filter(pg_get_database_ddl) FROM pg_get_database_ddl('regression_database_ddl', 'pretty', 'true', 'tablespace', 'false')"
);
is( $result,
	"CREATE DATABASE regression_database_ddl
    WITH TEMPLATE = template0
    ENCODING = 'UTF8';
ALTER DATABASE regression_database_ddl OWNER TO regress_datdba;
ALTER DATABASE regression_database_ddl CONNECTION LIMIT = 123;
ALTER DATABASE regression_database_ddl SET random_page_cost TO '2.0';",
	'database DDL pretty-printed');

# Permission check: revoke CONNECT on database
$node->safe_psql(
	'postgres', q{
CREATE ROLE regress_db_ddl_noaccess;
REVOKE CONNECT ON DATABASE regression_database_ddl FROM PUBLIC;
});
($ret, $stdout, $stderr) = $node->psql('postgres',
	"SET ROLE regress_db_ddl_noaccess; SELECT * FROM pg_get_database_ddl('regression_database_ddl')"
);
isnt($ret, 0, 'permission denied without CONNECT');
like(
	$stderr,
	qr/permission denied for database regression_database_ddl/,
	'permission error message');

# Cleanup
$node->safe_psql(
	'postgres', q{
GRANT CONNECT ON DATABASE regression_database_ddl TO PUBLIC;
DROP ROLE regress_db_ddl_noaccess;
DROP DATABASE regression_database_ddl;
DROP FUNCTION ddl_filter(text);
DROP ROLE regress_datdba;
});

$node->stop;

done_testing();
