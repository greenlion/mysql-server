#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2003 Jenny Zhang & Open Source Development Lab, Inc.
#

# 2004 July 16 : Reworked by Mark Wong
# 2004 September 28 : Turn this into a wrapper script because we don't know
#                     how long the test will execute so we collect stats
#                     until the test is done.  Because of the way things are
#                     run in the background and we wait for processs to
#                     complete, we only want to wait for the processes that
#                     are executing the queries.

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9

USE_OPROFILE=0

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
        sudo opstack > $OUTPUT_DIR/oprofile/call-graph.txt
}

TEST_ARGS=

while getopts "ef:n:o:p:s:t:y" opt; do
	case $opt in
	e) TEST_ARGS="$TEST_ARGS -e"
		;;
	f) scale_factor=$OPTARG
		;;
	n) num_stream=$OPTARG
		;;
	o) OUTPUT_DIR=$OPTARG
	   mkdir -p $OUTPUT_DIR/results
		;;
	p) PARAMETERS="${THROUGHPUT_PARAMETERS} $OPTARG"
		;;
	s) SEED_FILE=$OPTARG
		;;
	t) TAG=$OPTARG
		;;
	y) USE_OPROFILE=1
		;;
	esac
done

SEED=`cat $SEED_FILE`
echo "Seed : $SEED" > $OUTPUT_DIR/readme.txt

RUNDIR=$OUTPUT_DIR/run
mkdir -p $RUNDIR

DBSCRIPTDIR=$SRCDIR/scripts/pgsql
parsequery_dir="$SRCDIR/dbdriver/utils"

DBSTATS="$DBSCRIPTDIR/db_stats.sh"

# Clear the read profile counters.
if [ -f /proc/profile ]; then
	clearprof
fi

# Clear the oprofile counters.
if [ $USE_OPROFILE -eq 1 ]; then
	clearoprof
fi

${SHELL} $DBSCRIPTDIR/stop_db.sh || exit 1
${SHELL} $DBSCRIPTDIR/start_db.sh -o ${OUTPUT_DIR} -p "${PARAMETERS}" || exit 1

s_time=`$GTIME`
${SHELL} $DBSCRIPTDIR/record_start.sh -n "PERF${TAG}.THRUPUT" || exit 1

# Start collecting system statistics. 
${SHELL} $SRCDIR/scripts/start_sysstats.sh -o $OUTPUT_DIR || exit 1

# Start collecting database statistics.
${SHELL} $DBSTATS $SID $OUTPUT_DIR &

# Start the streams.
${SHELL} $DBSCRIPTDIR/throughput_stream_wrapper.sh -f $scale_factor -t $TAG -n $num_stream $TEST_ARGS -o $OUTPUT_DIR -s ${SEED_FILE} || exit 1

# Stop collecting system statistics.
${SHELL} $SRCDIR/scripts/stop_sysstats.sh $OUTPUT_DIR || exit 1

${SHELL} $DBSCRIPTDIR/record_end.sh -n "PERF${TAG}.THRUPUT" || exit 1
e_time=`$GTIME`
let "diff_time=$e_time-$s_time"
echo "Stream ${TAG} : Elapsed time for Throughput Test : $diff_time seconds"

# Stop the database after the test.
${SHELL} $DBSCRIPTDIR/stop_db.sh || exit 1

if [ -f /proc/profile ]; then
	profname="Throughput_Test_$TAG"
	getprof
fi

if [ $USE_OPROFILE -eq 1 ]; then
	profname="Throughput_Test_$TAG"
	getoprof
fi

exit 0
