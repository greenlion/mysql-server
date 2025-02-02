#!/bin/sh

DIR=`dirname $0`
. ${DIR}/dbt3_profile || exit 1

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9

if [ $# -ne 1 ]; then
	echo "usage: gen_data.sh <scale factore>"
fi

SF=$1

rm -f $DSS_PATH/customer.tbl $DSS_PATH/lineitem.tbl $DSS_PATH/nation.tbl $DSS_PATH/orders.tbl $DSS_PATH/part.tbl $DSS_PATH/partsupp.tbl $DSS_PATH/region.tbl $DSS_PATH/supplier.tbl

$DBGEN -s $SF -T c &
$DBGEN -s $SF -T L &
$DBGEN -s $SF -T n &
$DBGEN -s $SF -T O &
$DBGEN -s $SF -T P &
$DBGEN -s $SF -T r &
$DBGEN -s $SF -T s &
$DBGEN -s $SF -T S &

wait
