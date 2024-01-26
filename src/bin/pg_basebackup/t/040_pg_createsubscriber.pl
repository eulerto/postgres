# Copyright (c) 2024, PostgreSQL Global Development Group

#
# Test checking options of pg_createsubscriber.
#

use strict;
use warnings;
use PostgreSQL::Test::Utils;
use Test::More;

program_help_ok('pg_createsubscriber');
program_version_ok('pg_createsubscriber');
program_options_handling_ok('pg_createsubscriber');

my $datadir = PostgreSQL::Test::Utils::tempdir;

command_fails(['pg_createsubscriber'],
	'no subscriber data directory specified');
command_fails(
	[
		'pg_createsubscriber',
		'--pgdata', $datadir
	],
	'no publisher connection string specified');
command_fails(
	[
		'pg_createsubscriber',
		'--dry-run',
		'--pgdata', $datadir,
		'--publisher-conninfo', 'dbname=postgres'
	],
	'no subscriber connection string specified');
command_fails(
	[
		'pg_createsubscriber',
		'--verbose',
		'--pgdata', $datadir,
		'--publisher-conninfo', 'dbname=postgres',
		'--subscriber-conninfo', 'dbname=postgres'
	],
	'no database name specified');

done_testing();
