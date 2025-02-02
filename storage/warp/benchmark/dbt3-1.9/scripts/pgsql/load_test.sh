#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2002 Jenny Zhang & Open Source Development Lab, Inc.
#

# 15 July 2004 - Revamped by Mark Wong

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9

DBSCRIPTDIR=$SRCDIR/scripts/pgsql

DBSTATS="$DBSCRIPTDIR/db_stats.sh"

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

PARAMETERS=""
SF=0
USE_OPROFILE=0
GENERATE=0
ONLY_LOAD=0
while getopts "f:g:lo:p:tyv" opt; do
	case $opt in
	f)
		SF=$OPTARG
		;;
	g)
		GENERATE=$OPTARG
		;;
	l)
		ONLY_LOAD=1
		;;
	o)
		OUTPUT_DIR=$OPTARG
		mkdir -p $OUTPUT_DIR
		;;
	p)
		PARAMETERS="${LOAD_PARAMETERS} $OPTARG"
		;;
	t)
		TABLESPACE_FLAG="-t"
		;;
	v)
		set -x
		SHELL="${SHELL} -x"
		;;
	y)
		USE_OPROFILE=1
		;;
	?)
		echo "Usage: $0 [-o <dir> -p <db_param> -f <scale_factor>]"
		exit 1
	esac
done

if [ $GENERATE -ne 0 ]; then
	echo "Generating data for scale factor $SF..."
	date
	${DBGEN} -s $SF || exit 1
	chmod a+r ${DSS_PATH}/*.tbl
	date
else
	echo "Create the database using existing datafiles."
fi

# Initialize profile counters.
if [ -f /proc/profile ]; then
	clearprof
fi

if [ $USE_OPROFILE -eq 1 ]; then
	clearoprof
fi

# Start collecting system statistics.
${SHELL} $SRCDIR/scripts/start_sysstats.sh -o $OUTPUT_DIR

${SHELL} $DBSCRIPTDIR/create_db.sh -o ${OUTPUT_DIR} -p "${PARAMETERS}" || exit 1
	
${SHELL} $DBSCRIPTDIR/create_tables.sh ${TABLESPACE_FLAG} || exit 1

echo "`date +'%Y-%m-%d %H:%M:%S'` Starting Load Test..."
s_time=`$GTIME`
${SHELL} $DBSCRIPTDIR/record_start.sh -n "LOAD"

# Collect database statistics
${SHELL} $DBSTATS $SID $OUTPUT_DIR &

date
${SHELL} ${DBSCRIPTDIR}/load_db.sh ${TABLESPACE_FLAG} || exit 1
date

if [ ${ONLY_LOAD} -eq 0 ]; then
	date
	${SHELL} $DBSCRIPTDIR/create_indexes.sh ${TABLESPACE_FLAG} || exit 1
	date
	
	date
	${SHELL} $DBSCRIPTDIR/update_statistics.sh || exit 1
	date
fi

${SHELL} $DBSCRIPTDIR/record_end.sh -n "LOAD" || exit 1
e_time=`$GTIME`
echo "`date +'%Y-%m-%d %H:%M:%S'` Load Test Completed"
let "diff_time=$e_time-$s_time"
echo "Elapsed time for Load Test : $diff_time seconds"

# Stop collecting system statistics.
${SHELL} $SRCDIR/scripts/stop_sysstats.sh $OUTPUT_DIR

# Collect profile data.
if [ -f /proc/profile ]; then
	profname='Load_Test'
	getprof
fi

if [ $USE_OPROFILE -eq 1 ]; then
	profname='Load_Test'
	getoprof
fi

exit 0
