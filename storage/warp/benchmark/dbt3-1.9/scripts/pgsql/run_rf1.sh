#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2003 Open Source Development Lab, Inc.
#

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9

if [ $# -ne 2 ]; then
        echo "Usage: ./run_rf1.sh <scale_factor> <run dir>"
        exit 1
fi

scale_factor=$1
RUNDIR=$2

curr_set_file_rf1="$RUNDIR/curr_set_num_rf1"
lock_file_rf1="$RUNDIR/rf1.lock"
min_set_file="$RUNDIR/min_set_num"
max_set_file="$RUNDIR/max_set_num"

# if curr_set_file does not exist, we generate 12 update sets
# create a semaphore file so that only one process can access
# $curr_set_file_rf1 
lockfile -s 0 $lock_file_rf1
if [ ! -f $curr_set_file_rf1 ];
then
	echo "generating update set 1 - 12"
	$DBGEN -s $scale_factor -U 12
	echo "1" > ${min_set_file}
	echo "12" > ${max_set_file}
	echo "0" > ${curr_set_file_rf1}
fi
rm -f $lock_file_rf1

lockfile -s 0 $lock_file_rf1
set_num=`cat $curr_set_file_rf1`
min_set=`cat $min_set_file`
max_set=`cat $max_set_file`

let "set_num=$set_num+1"
echo $set_num>$curr_set_file_rf1

# if the current set number is larger than max_set, we need to generate new set
if [ $set_num -gt $max_set ]
then
	let "min_set=$min_set+12"
	let "max_set=$max_set+12"
	echo "Stream ${set_num} : Generating update set $min_set - $max_set..."
	$DBGEN -s $scale_factor -U $max_set
	echo "$min_set" > ${min_set_file}
	echo "$max_set" > ${max_set_file}
fi
rm -f $lock_file_rf1

echo "`date`: Stream ${set_num} : Starting Refresh Stream 1..."
s_time=`$GTIME`

# generating the load .sql
echo "COPY tmp_lineitem$set_num FROM '/tmp/lineitem.tbl.u$set_num' USING DELIMITERS '|';" >> tmp_lineitem$set_num.sql

echo "COPY tmp_orders$set_num FROM '/tmp/orders.tbl.u$set_num' USING DELIMITERS '|';" >> tmp_orders$set_num.sql

/usr/bin/psql -d $SID -c "create table tmp_lineitem$set_num (l_orderkey numeric(10), l_partkey numeric(10), l_suppkey numeric(10), l_linenumber numeric(10), l_quantity numeric(12,2), l_extendedprice numeric(12,2), l_discount numeric(12,2), l_tax numeric(12,2), l_returnflag char(1), l_linestatus char(1), l_shipdate date, l_commitdate date, l_receiptdate date, l_shipinstruct char(25), l_shipmode char(10), l_comment varchar(44));"

/usr/bin/psql -d $SID -f tmp_lineitem$set_num.sql

/usr/bin/psql -d $SID -c "insert into lineitem (select * from tmp_lineitem$set_num);"

/usr/bin/psql -d $SID -c "create table tmp_orders$set_num (o_orderkey numeric(10), o_custkey numeric(10), o_orderstatus char(1), o_totalprice numeric(12,2), o_orderdate date, o_orderpriority char(15), o_clerk char(15), o_shippriority numeric(10), o_comment varchar(79));"

/usr/bin/psql -d $SID -f tmp_orders$set_num.sql

/usr/bin/psql -d $SID -c "insert into orders (select * from tmp_orders$set_num);"

# clean up
/usr/bin/psql -d $SID -c "drop table tmp_lineitem$set_num;"

/usr/bin/psql -d $SID -c "drop table tmp_orders$set_num;"
rm -f tmp_lineitem$set_num.sql
rm -f tmp_orders$set_num.sql

e_time=`$GTIME`
echo "`date`: Stream ${set_num} : Refresh Stream 1 completed."
let "diff_time=$e_time-$s_time"
echo "Stream ${set_num} : Elapsed time for Refresh Stream 1 : $diff_time seconds"

exit 0
