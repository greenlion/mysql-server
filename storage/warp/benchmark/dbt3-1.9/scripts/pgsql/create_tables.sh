#!/bin/bash

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2005 Jenny Zhang & Open Source Development Labs, Inc.
#

DIR=`dirname $0`
. ${DIR}/pgsql_profile || exit 1

USE_TABLESPACES=0
while getopts "t" OPT; do
	case ${OPT} in
	t)
		USE_TABLESPACES=1
		;;
	esac
done

PSQL="/usr/bin/psql -e -d ${SID} -c"

if [ ${USE_TABLESPACES} -eq 1 ]; then
	TS_SUPPLIER_DIR="${TSDIR}/supplier/ts"
	TS_PART_DIR="${TSDIR}/part/ts"
	TS_PARTSUPP_DIR="${TSDIR}/partsupp/ts"
	TS_CUSTOMER_DIR="${TSDIR}/customer/ts"
	TS_ORDERS_DIR="${TSDIR}/orders/ts"
	TS_LINEITEM_DIR="${TSDIR}/lineitem/ts"
	TS_NATION_DIR="${TSDIR}/nation/ts"
	TS_REGION_DIR="${TSDIR}/region/ts"

	mkdir -p ${TS_SUPPLIER_DIR}
	mkdir -p ${TS_PART_DIR}
	mkdir -p ${TS_PARTSUPP_DIR}
	mkdir -p ${TS_CUSTOMER_DIR}
	mkdir -p ${TS_ORDERS_DIR}
	mkdir -p ${TS_LINEITEM_DIR}
	mkdir -p ${TS_NATION_DIR}
	mkdir -p ${TS_REGION_DIR}

	SUPPLIER_TABLESPACE="TABLESPACE dbt3_supplier"
	PART_TABLESPACE="TABLESPACE dbt3_part"
	PARTSUPP_TABLESPACE="TABLESPACE dbt3_partsupp"
	CUSTOMER_TABLESPACE="TABLESPACE dbt3_customer"
	ORDERS_TABLESPACE="TABLESPACE dbt3_orders"
	LINEITEM_TABLESPACE="TABLESPACE dbt3_lineitem"
	NATION_TABLESPACE="TABLESPACE dbt3_nation"
	REGION_TABLESPACE="TABLESPACE dbt3_region"

	${PSQL} "CREATE ${SUPPLIER_TABLESPACE} LOCATION '${TS_SUPPLIER_DIR}';"
	${PSQL} "CREATE ${PART_TABLESPACE} LOCATION '${TS_PART_DIR}';"
	${PSQL} "CREATE ${PARTSUPP_TABLESPACE} LOCATION '${TS_PARTSUPP_DIR}';"
	${PSQL} "CREATE ${CUSTOMER_TABLESPACE} LOCATION '${TS_CUSTOMER_DIR}';"
	${PSQL} "CREATE ${ORDERS_TABLESPACE} LOCATION '${TS_ORDERS_DIR}';"
	${PSQL} "CREATE ${LINEITEM_TABLESPACE} LOCATION '${TS_LINEITEM_DIR}';"
	${PSQL} "CREATE ${NATION_TABLESPACE} LOCATION '${TS_NATION_DIR}';"
	${PSQL} "CREATE ${REGION_TABLESPACE} LOCATION '${TS_REGION_DIR}';"
fi

${PSQL} "
CREATE TABLE supplier (
	s_suppkey  INTEGER,
	s_name CHAR(25),
	s_address VARCHAR(40),
	s_nationkey INTEGER,
	s_phone CHAR(15),
	s_acctbal REAL,
	s_comment VARCHAR(101))
	${SUPPLIER_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE part (
	p_partkey INTEGER,
	p_name VARCHAR(55),
	p_mfgr CHAR(25),
	p_brand CHAR(10),
	p_type VARCHAR(25),
	p_size INTEGER,
	p_container CHAR(10),
	p_retailprice REAL,
	p_comment VARCHAR(23))
	${PART_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE partsupp (
	ps_partkey INTEGER,
	ps_suppkey INTEGER,
	ps_availqty INTEGER,
	ps_supplycost REAL,
	ps_comment VARCHAR(199))
	${PARTSUPP_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE customer (
	c_custkey INTEGER,
	c_name VARCHAR(25),
	c_address VARCHAR(40),
	c_nationkey INTEGER,
	c_phone CHAR(15),
	c_acctbal REAL,
	c_mktsegment CHAR(10),
	c_comment VARCHAR(117))
	${CUSTOMER_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE orders (
	o_orderkey INTEGER,
	o_custkey INTEGER,
	o_orderstatus CHAR(1),
	o_totalprice REAL,
	o_orderDATE DATE,
	o_orderpriority CHAR(15),
	o_clerk CHAR(15),
	o_shippriority INTEGER,
	o_comment VARCHAR(79))
	${ORDERS_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE lineitem (
	l_orderkey INTEGER,
	l_partkey INTEGER,
	l_suppkey INTEGER,
	l_linenumber INTEGER,
	l_quantity REAL,
	l_extendedprice REAL,
	l_discount REAL,
	l_tax REAL,
	l_returnflag CHAR(1),
	l_linestatus CHAR(1),
	l_shipDATE DATE,
	l_commitDATE DATE,
	l_receiptDATE DATE,
	l_shipinstruct CHAR(25),
	l_shipmode CHAR(10),
	l_comment VARCHAR(44))
	${LINEITEM_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE nation (
	n_nationkey INTEGER,
	n_name CHAR(25),
	n_regionkey INTEGER,
	n_comment VARCHAR(152))
	${NATION_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE region (
	r_regionkey INTEGER,
	r_name CHAR(25),
	r_comment VARCHAR(152))
	${REGION_TABLESPACE};
" || exit 1

${PSQL} "
CREATE TABLE time_statistics (
	task_name VARCHAR(40),
	s_time TIMESTAMP,
	e_time TIMESTAMP,
	int_time INTEGER);
" || exit 1

exit 0
