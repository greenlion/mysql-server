#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2003 Jenny Zhang & Open Source Development Lab, Inc.
#

# 15 July 2004: Reworked by Mark Wong

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9

clearprof () {
	sudo /usr/sbin/readprofile -m /boot/System.map -r
}

getprof () {
	sudo /usr/sbin/readprofile -n -m /boot/System.map -v | sort -grk3,4 > $OUTPUT_DIR/readprofile.txt
}

clearoprof () {
	sudo opcontrol --vmlinux=/boot/vmlinux
	sleep 2
	sudo opcontrol --start-daemon
	sleep 2
	sudo opcontrol --start
	sleep 2
	# If opcontrol ever gets stuck here, sometimes it helps to remove
	# everything in this dir:
	# /var/lib/oprofile
	sudo opcontrol --reset
}

getoprof () {
	mkdir -p $OUTPUT_DIR/oprofile/annotate
	sudo opcontrol --dump
	sudo opreport -l -o $OUTPUT_DIR/oprofile/oprofile.txt
	sudo opcontrol --stop
	sudo opcontrol --shutdown
	cp -pR /var/lib/oprofile/samples/current $OUTPUT_DIR/oprofile/
	sudo opannotate --source --assembly > $OUTPUT_DIR/oprofile/assembly.txt 2>&1
	sudo opannotate --source --output-dir=$OUTPUT_DIR/oprofile/annotate
	sudo opstack > $OUTPUT_DIR/oprofile//call-graph.txt
}

EXPLAIN_ANALYZE=0
USE_OPROFILE=0

# process the command line parameters
while getopts "ef:p:o:s:t:y" opt; do
	case $opt in
		e) EXPLAIN_ANALYZE=1
			;;
		f) SCALE_FACTOR=$OPTARG
			;;
		o) OUTPUT_DIR=$OPTARG
		   mkdir -p $OUTPUT_DIR/results
			;;
		p) PARAMETERS="${POWER_PARAMETERS} $OPTARG"
			;;
		s) SEED_FILE=$OPTARG
			;;
		t) TAG=$OPTARG
			;;
		y) USE_OPROFILE=1
			;;
		?) echo "Usage: $0 -f <SCALE_FACTOR> [-e -p <db_params> -t <tag> -y]"
			exit ;;
		esac
done

RUNDIR=$OUTPUT_DIR/run
mkdir -p $RUNDIR

SCRIPTDIR=$SRCDIR/scripts
DBSCRIPTDIR=$SRCDIR/scripts/pgsql

param_file="$RUNDIR/power_plan.para"
query_file="$RUNDIR/power_plan.sql"
tmp_query_file="$RUNDIR/tmp_power_plan.sql"

DBSTATS="$DBSCRIPTDIR/db_stats.sh"

# Generate queries for the Power test.
SEED=`cat $SEED_FILE`
echo "Seed : $SEED" > $OUTPUT_DIR/readme.txt
${QGEN} -c -r $SEED -p 0 -s $SCALE_FACTOR -l $param_file -x > $query_file

# Get the EXPLAIN plans for only the SELECT statements.
PLANDIR=$OUTPUT_DIR/db/plans
mkdir -p $PLANDIR
i=1
while [ $i -le 22 ]
do
	if [ $i -ne 15 ]; then
		${SHELL} $DBSCRIPTDIR/get_query_plan.sh $SCALE_FACTOR $i $PLANDIR/power_query$i.txt $RUNDIR $SEED_FILE
	fi
	let "i=$i+1"
done
# Modify query file so that the commands are in one line.
${PARSE_QUERY} $query_file $tmp_query_file E

${SHELL} $DBSCRIPTDIR/stop_db.sh || exit 1
${SHELL} $DBSCRIPTDIR/start_db.sh -o ${OUTPUT_DIR} -p "${PARAMETERS}" || exit 1

# Start collecting system statistics.
${SHELL} $SCRIPTDIR/start_sysstats.sh -o $OUTPUT_DIR || exit 1

# Collect database statistics
${SHELL} $DBSTATS $SID $OUTPUT_DIR &

# Clear the read profile counters.
if [ -f /proc/profile ]; then
	clearprof
fi

# Clear the oprofile counters.
if [ $USE_OPROFILE -eq 1 ]; then
	clearoprof
fi

s_time_power=`$GTIME`
${SHELL} $DBSCRIPTDIR/record_start.sh -n "PERF${TAG}.POWER" || exit 1

# Refresh Stream 1
echo "`date`: Power Test : Starting Refresh Stream 1" 
s_time=`$GTIME`
${SHELL} $DBSCRIPTDIR/record_start.sh -n "PERF${TAG}.POWER.RF1" || exit 1
${SHELL} $DBSCRIPTDIR/run_rf1.sh $SCALE_FACTOR $RUNDIR > $OUTPUT_DIR/results/power.perf${TAG}.rf1.result 2>&1 || exit 1
${SHELL} $DBSCRIPTDIR/record_end.sh -n "PERF${TAG}.POWER.RF1" || exit 1
e_time=`$GTIME`
echo "`date`: Power Test : Refresh Stream 1 completed." 
let "diff_time=$e_time-$s_time"

# Execute the queries.
${SHELL} $DBSCRIPTDIR/run_power_query.sh $SCALE_FACTOR $TAG $EXPLAIN_ANALYZE $OUTPUT_DIR $RUNDIR $SEED_FILE || exit 1

# Refresh Stream 2
echo "`date`: Power Test : Starting Refresh Stream 2" 
s_time=`$GTIME`
${SHELL} $DBSCRIPTDIR/record_start.sh -n "PERF${TAG}.POWER.RF2" || exit 1
${SHELL} $DBSCRIPTDIR/run_rf2.sh $RUNDIR > $OUTPUT_DIR/results/power.perf${TAG}.rf2.result 2>&1 || exit 1
${SHELL} $DBSCRIPTDIR/record_end.sh -n "PERF${TAG}.POWER.RF2" || exit 1
e_time=`$GTIME`
echo "`date`: Power Test : Refresh Stream 2 completed." 
let "diff_time=$e_time-$s_time"

${SHELL} $DBSCRIPTDIR/record_end.sh -n "PERF${TAG}.POWER" || exit 1
e_time_power=`$GTIME`
echo "`date`: Power Test completed."
let "diff_time=$e_time_power-$s_time_power"
echo "Elapsed time for Power Test : $diff_time seconds"

# Stop collecting system statistics.
${SHELL} $SCRIPTDIR/stop_sysstats.sh $OUTPUT_DIR

${SHELL} $DBSCRIPTDIR/stop_db.sh || exit 1

if [ -f /proc/profile ]; then
	profname="Power_Test_$TAG"
	getprof
fi

if [ $USE_OPROFILE -eq 1 ]; then
	profname="Power_Test_$TAG"
	getoprof
fi

exit 0
