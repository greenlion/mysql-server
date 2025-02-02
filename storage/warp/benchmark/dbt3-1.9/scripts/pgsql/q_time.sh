#!/bin/bash
# q_time.sh: get task execution times
#
# This file is released under the terms of the Artistic License.  Please see
# the file LICENSE, included in this package, for details.
#
# Copyright (C) 2003 Jenny Zhang & Open Source Development Lab, Inc.
#
# Author: Jenny Zhang
# Heavily modified by: Mark Wong

DIR=`dirname $0`
. ${DIR}/pgsql_profile

SQL="SELECT task_name, s_time, e_time, (e_time-s_time) AS diff_time, (extract(hour FROM (e_time-s_time)) * 3600) + (extract(minute FROM (e_time-s_time)) * 60) + (extract(second FROM (e_time-s_time))) AS seconds FROM time_statistics;"
ARGS=
while getopts "ho:" opt; do
	case $opt in
		h)
			ARGS="-H"
			SQL="SELECT task_name AS Task, s_time AS Start_Time, e_time AS End_Time, (e_time-s_time) AS Elapsed_Time FROM time_statistics;"
			;;
		o)
			ARGS="-o $OPTARG/q_time.out"
			;;
	esac
done


/usr/bin/psql -d $SID -q -c "${SQL}" $ARGS
