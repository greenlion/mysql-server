#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see # the file LICENSE, included in this package, for details.
#
# Copyright (C) 2004 Mark Wong & Jenny Zhang & Open Source Development Lab, Inc.
#

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9

EXPLAIN_ANALYZE=0
while getopts "ef:n:o:s:t:" opt; do
	case $opt in
	e) EXPLAIN_ANALYZE=1
		;;
	f) scale_factor=$OPTARG
		;;
	n) num_stream=$OPTARG
		;;
	o) OUTPUT_DIR=$OPTARG
		;;
	s) SEED_FILE=$OPTARG
		;;
	t) TAG=$OPTARG
		;;
	esac
done

RUNDIR=$OUTPUT_DIR/run

DBSCRIPTDIR=$SRCDIR/scripts/pgsql

# Start each stream.
i=1
while [ $i -le $num_stream ] 
do
	bash $DBSCRIPTDIR/run_throughput_stream.sh $scale_factor $TAG $i $EXPLAIN_ANALYZE $OUTPUT_DIR $SEED_FILE > $RUNDIR/thruput_qs$i 2>&1 || exit 1 &
	
	let "i=$i+1"
done

# Start the refresh stream.  The throughput tests runs a streams consecutively
# per throughput streams, also consecutively.
stream_num=1
while [ $stream_num -le $num_stream ]
do
#	s_time_stream=`$GTIME`
	bash $DBSCRIPTDIR/record_start.sh -n "PERF${TAG}.THRUPUT.RFST${stream_num}"

	echo "`date`: Throughput Stream $stream_num : Starting Refresh Stream 1..."
	s_time_rf1=`$GTIME`
	bash $DBSCRIPTDIR/record_start.sh -n "PERF${TAG}.THRUPUT.RFST${stream_num}.RF1"
	bash $DBSCRIPTDIR/run_rf1.sh $scale_factor $RUNDIR > $OUTPUT_DIR/results/thruput.perf${TAG}.stream${stream_num}.rf1.result 2>&1 || exit 1
	bash $DBSCRIPTDIR/record_end.sh -n "PERF${TAG}.THRUPUT.RFST${stream_num}.RF1"
	e_time_rf1=`$GTIME`
	echo "`date`: Throughput Stream $stream_num : Refresh Stream 1 completed."
	let "diff_time_rf1=$e_time_rf1-$s_time_rf1"
	echo "Throughput Stream $stream_num : Elapsed time for Refresh Stream 1 : $diff_time_rf1 seconds"

	echo "`date`: Throughput Stream $stream_num : Starting Refresh Stream 2..."
	s_time_rf2=`$GTIME`
	bash $DBSCRIPTDIR/record_start.sh -n "PERF${TAG}.THRUPUT.RFST${stream_num}.RF2"
	bash $DBSCRIPTDIR/run_rf2.sh $RUNDIR > $OUTPUT_DIR/results/thruput.perf${TAG}.stream${stream_num}.rf2.result 2>&1 || exit 1
	bash $DBSCRIPTDIR/record_end.sh -n "PERF${TAG}.THRUPUT.RFST${stream_num}.RF2"
	e_time_rf2=`$GTIME`
	echo "`date`: Throughput Stream $stream_num : Refresh Stream 2 completed."
	let "diff_time_rf2=$e_time_rf2-$s_time_rf2"
	echo "Throughput Stream $stream_num : Elapsed time for Refresh Stream 2 : $diff_time_rf2 seconds"

	bash $DBSCRIPTDIR/record_end.sh -n "PERF${TAG}.THRUPUT.RFST${stream_num}"
#	e_time_stream=`$GTIME`
#	let "diff_time_stream=$e_time_stream-$s_time_stream"

        let "stream_num=$stream_num+1"
done

wait

exit 0
