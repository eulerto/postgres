# Copyright (c) 2024, PostgreSQL Global Development Group

#
# Test using a standby server as the subscriber.

use strict;
use warnings;
use PostgreSQL::Test::Cluster;
use PostgreSQL::Test::Utils;
use Test::More;

my $node_p;
my $node_f;
my $node_s;
my $node_c;
my $result;
my $slotname;

# Set up node P as primary
$node_p = PostgreSQL::Test::Cluster->new('node_p');
$node_p->init(allows_streaming => 'logical');
$node_p->start;

# Set up node F as about-to-fail node
# Force it to initialize a new cluster instead of copying a
# previously initdb'd cluster.
{
	local $ENV{'INITDB_TEMPLATE'} = undef;

	$node_f = PostgreSQL::Test::Cluster->new('node_f');
	$node_f->init(allows_streaming => 'logical');
	$node_f->start;
}

# On node P
# - create databases
# - create test tables
# - insert a row
# - create a physical replication slot
$node_p->safe_psql(
	'postgres', q(
	CREATE DATABASE pg1;
	CREATE DATABASE pg2;
));
$node_p->safe_psql('pg1', 'CREATE TABLE tbl1 (a text)');
$node_p->safe_psql('pg1', "INSERT INTO tbl1 VALUES('first row')");
$node_p->safe_psql('pg2', 'CREATE TABLE tbl2 (a text)');
$slotname = 'physical_slot';
$node_p->safe_psql('pg2',
	"SELECT pg_create_physical_replication_slot('$slotname')");

# Set up node S as standby linking to node P
$node_p->backup('backup_1');
$node_s = PostgreSQL::Test::Cluster->new('node_s');
$node_s->init_from_backup($node_p, 'backup_1', has_streaming => 1);
$node_s->append_conf(
	'postgresql.conf', qq[
log_min_messages = debug2
primary_slot_name = '$slotname'
]);
$node_s->set_standby_mode();

# Run pg_createsubscriber on about-to-fail node F
command_fails(
	[
		'pg_createsubscriber', '--verbose',
		'--pgdata', $node_f->data_dir,
		'--publisher-server', $node_p->connstr('pg1'),
		'--subscriber-server', $node_f->connstr('pg1'),
		'--database', 'pg1',
		'--database', 'pg2'
	],
	'subscriber data directory is not a copy of the source database cluster');

# Run pg_createsubscriber on the stopped node
command_fails(
	[
		'pg_createsubscriber', '--verbose',
		'--dry-run', '--pgdata',
		$node_s->data_dir, '--publisher-server',
		$node_p->connstr('pg1'), '--subscriber-server',
		$node_s->connstr('pg1'), '--database',
		'pg1', '--database',
		'pg2'
	],
	'target server must be running');

$node_s->start;

# Set up node C as standby linking to node S
$node_s->backup('backup_2');
$node_c = PostgreSQL::Test::Cluster->new('node_c');
$node_c->init_from_backup($node_s, 'backup_2', has_streaming => 1);
$node_c->append_conf(
	'postgresql.conf', qq[
log_min_messages = debug2
]);
$node_c->set_standby_mode();
$node_c->start;

# Run pg_createsubscriber on node C (P -> S -> C)
command_fails(
	[
		'pg_createsubscriber', '--verbose',
		'--dry-run',
		'--pgdata',	$node_c->data_dir,
		'--publisher-server', $node_s->connstr('pg1'),
		'--subscriber-server', $node_c->connstr('pg1'),
		'--database', 'pg1',
		'--database', 'pg2'
	],
	'primary server is in recovery');

# Stop node C
$node_c->teardown_node;

# Insert another row on node P and wait node S to catch up
$node_p->safe_psql('pg1', "INSERT INTO tbl1 VALUES('second row')");
$node_p->wait_for_replay_catchup($node_s);

# dry run mode on node S
command_ok(
	[
		'pg_createsubscriber', '--verbose',
		'--dry-run', '--pgdata',
		$node_s->data_dir, '--publisher-server',
		$node_p->connstr('pg1'), '--subscriber-server',
		$node_s->connstr('pg1'), '--database',
		'pg1', '--database',
		'pg2'
	],
	'run pg_createsubscriber --dry-run on node S');

# Check if node S is still a standby
is($node_s->safe_psql('postgres', 'SELECT pg_catalog.pg_is_in_recovery()'),
	't', 'standby is in recovery');

# pg_createsubscriber can run without --databases option
command_ok(
	[
		'pg_createsubscriber', '--verbose',
		'--dry-run', '--pgdata',
		$node_s->data_dir, '--publisher-server',
		$node_p->connstr('pg1'), '--subscriber-server',
		$node_s->connstr('pg1')
	],
	'run pg_createsubscriber without --databases');

# Run pg_createsubscriber on node S
command_ok(
	[
		'pg_createsubscriber', '--verbose',
		'--pgdata', $node_s->data_dir,
		'--publisher-server', $node_p->connstr('pg1'),
		'--subscriber-server', $node_s->connstr('pg1'),
		'--database', 'pg1',
		'--database', 'pg2'
	],
	'run pg_createsubscriber on node S');

ok( -d $node_s->data_dir . "/pg_createsubscriber_output.d",
	"pg_createsubscriber_output.d/ removed after pg_createsubscriber success"
);

# Confirm the physical replication slot has been removed
$result = $node_p->safe_psql('pg1',
	"SELECT count(*) FROM pg_replication_slots WHERE slot_name = '$slotname'"
);
is($result, qq(0),
	'the physical replication slot used as primary_slot_name has been removed'
);

# Insert rows on P
$node_p->safe_psql('pg1', "INSERT INTO tbl1 VALUES('third row')");
$node_p->safe_psql('pg2', "INSERT INTO tbl2 VALUES('row 1')");

# PID sets to undefined because subscriber was stopped behind the scenes.
# Start subscriber
$node_s->{_pid} = undef;
$node_s->start;

# Get subscription names
$result = $node_s->safe_psql(
	'postgres', qq(
	SELECT subname FROM pg_subscription WHERE subname ~ '^pg_createsubscriber_'
));
my @subnames = split("\n", $result);

# Wait subscriber to catch up
$node_s->wait_for_subscription_sync($node_p, $subnames[0]);
$node_s->wait_for_subscription_sync($node_p, $subnames[1]);

# Check result on database pg1
$result = $node_s->safe_psql('pg1', 'SELECT * FROM tbl1');
is( $result, qq(first row
second row
third row),
	'logical replication works on database pg1');

# Check result on database pg2
$result = $node_s->safe_psql('pg2', 'SELECT * FROM tbl2');
is($result, qq(row 1), 'logical replication works on database pg2');

# Different system identifier?
my $sysid_p = $node_p->safe_psql('postgres',
	'SELECT system_identifier FROM pg_control_system()');
my $sysid_s = $node_s->safe_psql('postgres',
	'SELECT system_identifier FROM pg_control_system()');
ok($sysid_p != $sysid_s, 'system identifier was changed');

# clean up
$node_p->teardown_node;
$node_s->teardown_node;
$node_f->teardown_node;

done_testing();
