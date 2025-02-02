#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2003 Open Source Development Lab, Inc.
#

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9

RUNDIR=$1

curr_set_file_rf1="$RUNDIR/curr_set_num_rf1"
curr_set_file_rf2="$RUNDIR/curr_set_num_rf2"
lock_file_rf1="$RUNDIR/rf1.lock"
lock_file_rf2="$RUNDIR/rf2.lock"

# if set_num_file_rf1 does not exist, exit since rf1 has to run before rf2
lockfile -s 0 $lock_file_rf1
if [ ! -f $curr_set_file_rf1 ];
then
        echo "Stream ${set_num} : please run run_rf1.sh first"
	exit 1
fi
set_num_rf1=`cat $curr_set_file_rf1`
rm -f $lock_file_rf1

lockfile -s 0 $lock_file_rf2
if [ ! -f $curr_set_file_rf2 ];
then
	echo 0 > $curr_set_file_rf2
fi

set_num=`cat $curr_set_file_rf2`

let "set_num=$set_num+1"
if [ $set_num -gt $set_num_rf1 ]
then
	echo "Stream ${set_num} : rf2 set number is greater than rf1 set number"
	echo "Stream ${set_num} : please execute run_rf1.sh first"
	exit 1
fi

echo $set_num > $curr_set_file_rf2
rm -f $lock_file_rf2

echo "`date`: Stream ${set_num} : Starting Refresh Stream 2..."
s_time=`$GTIME`

# generate load .sql
echo "COPY tmp_orderkey$set_num FROM '/tmp/delete.$set_num' USING DELIMITERS '|';" >> tmp_orderkey$set_num.sql

/usr/bin/psql -d $SID -c "create table tmp_orderkey$set_num (orderkey numeric(10));"

/usr/bin/psql -d $SID -f tmp_orderkey$set_num.sql

/usr/bin/psql -d $SID -c "delete from lineitem where l_orderkey=tmp_orderkey$set_num.orderkey;"

/usr/bin/psql -d $SID -c "delete from orders where o_orderkey=tmp_orderkey$set_num.orderkey;"

# clean up
/usr/bin/psql -d $SID -c "drop table tmp_orderkey$set_num;"
rm -f tmp_orderkey$set_num.sql

e_time=`$GTIME`
echo "`date`: Stream ${set_num} : Refresh Stream 2 completed."
let "diff_time=$e_time-$s_time"
echo "Stream ${set_num} : Elapsed time for Refresh Stream 2 : $diff_time seconds"

exit 0
