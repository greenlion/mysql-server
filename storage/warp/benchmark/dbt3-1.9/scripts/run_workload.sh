#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2004 Mark Wong & Jenny Zhang
#                    Open Source Development Labs, Inc.
#

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9
DATABASE=pgsql
SCRIPTDIR=$SRCDIR/scripts
DBSCRIPTDIR=$SRCDIR/scripts/$DATABASE

DIR=`dirname $0`
source ${DIR}/dbt3_profile || exit 1

SEED=0
REDIR_LOG=0
REDIR_TMP=0
SCALE_FACTOR=1
STREAMS=1
MAX=1
GENERATE=0
TEST_ARGS=
LOAD_ARGS=
while getopts "ef:gn:op:q:r:s:tuv" opt; do
	case $opt in
	e)
		# PostgreSQL only.
		TEST_ARGS="$TEST_ARGS -e"
		;;
	f)
		SCALE_FACTOR=$OPTARG
		;;
	g)
		GENERATE=1
		;;
	n)
		STREAMS=$OPTARG
		;;
	o)
		OPROFILE_FLAG="-y"
		;;
	p)
		# PostgreSQL only.
		LOAD_PARAMETERS="${DEFAULT_LOAD_PARAMETERS} $OPTARG"
		;;
	q)
		# PostgreSQL only.
		POWER_PARAMETERS="${DEFAULT_POWER_PARAMETERS} $OPTARG"
		;;
	r)
		# PostgreSQL only.
		THROUGHPUT_PARAMETERS="${DEFAULT_THROUGHPUT_PARAMETERS} $OPTARG"
		;;
	s)
		SEED=$OPTARG
		;;
	t)
		LOAD_ARGS="$LOAD_ARGS -t"
		;;
	u)
		TABLESPACES_FLAG="-t"
		;;
	v)
		SHELL="${SHELL} -x"
		export SHELL;
		;;
	esac
done

# Determine a unique identifer for this test run.
RUN_NUMBER=-1
if test -f run_number; then
	read RUN_NUMBER < run_number
fi
if [ $RUN_NUMBER -eq -1 ]; then
	RUN_NUMBER=0;
fi

# Create output directories.
OUTPUT_DIR=$SRCDIR/scripts/output/$RUN_NUMBER
mkdir -p $OUTPUT_DIR

# Set the seed file.
SEED_FILE=$OUTPUT_DIR/seed
if [ $SEED -eq 0 ]; then
	${SHELL} $SRCDIR/scripts/init_seed.sh > $SEED_FILE
else
	echo $SEED > $SEED_FILE
fi
echo "Using seed: `cat $SEED_FILE`"

# Load Test
${SHELL} $DBSCRIPTDIR/load_test.sh -o $OUTPUT_DIR/load -p "${LOAD_PARAMETERS}" ${OPROFILE_FLAG} -f $SCALE_FACTOR -g $GENERATE $LOAD_ARGS ${TABLESPACES_FLAG} || exit 1

i=1
while [ $i -le $MAX ]
do
	# Start time of a Power and Throughput test.
	s_time=`$GTIME`
	${SHELL} $DBSCRIPTDIR/record_start.sh -n "PERF${i}" || exit 1

	# Power Test
	${SHELL} $DBSCRIPTDIR/power_test.sh -f $SCALE_FACTOR -o $OUTPUT_DIR/power${i} -p "${POWER_PARAMETERS}" $TEST_ARGS -s ${SEED_FILE} -t $i ${OPROFILE_FLAG} || exit 1

	# Throughput Test
	${SHELL} $DBSCRIPTDIR/throughput_test.sh -n $STREAMS -f $SCALE_FACTOR -o $OUTPUT_DIR/throughput${i} -p "${THROUGHPUT_PARAMETERS}" $TEST_ARGS -s ${SEED_FILE} -t $i ${OPROFILE_FLAG} || exit 1

	# The database should be shut down after the last test, so start it back
	# up so we can update and retrieve test information in the database.
	${SHELL} $DBSCRIPTDIR/start_db.sh

	# End time of a Power and Throughput test.
	${SHELL} $DBSCRIPTDIR/record_end.sh -n "PERF${i}" || exit 1
	e_time=`$GTIME`
	let "diff_time=$e_time-$s_time"
	echo "Elapsed time for performance test ${i} : $diff_time seconds"

	# Increment loop counter.
	let "i=$i+1"
done

# Get system details.
${SHELL} $SCRIPTDIR/get_config.sh $SCALE_FACTOR $STREAMS "$LOAD_PARAMETERS" "$POWER_PARAMETERS" "$THROUGHPUT_PARAMETERS" $OUTPUT_DIR || exit 1

# Get query times.
${SHELL} $DBSCRIPTDIR/q_time.sh > $OUTPUT_DIR/q_time.out || exit 1

# Calculate composite score.      
${SHELL} $SRCDIR/scripts/get_composite.sh -i ${OUTPUT_DIR}/q_time.out -p 1 \
		-s ${SCALE_FACTOR} -n ${STREAMS} \
		-o ${OUTPUT_DIR}/calc_composite.out || exit 1
perl $SRCDIR/scripts/graph_query_time.pl --if $OUTPUT_DIR/q_time.out || exit 1
${SHELL} $SRCDIR/scripts/gen_html.sh $OUTPUT_DIR > $OUTPUT_DIR/index.html || exit 1

RUN_NUMBER=`expr $RUN_NUMBER + 1`
echo $RUN_NUMBER > run_number

echo "Results are in $OUTPUT_DIR"

exit 0
