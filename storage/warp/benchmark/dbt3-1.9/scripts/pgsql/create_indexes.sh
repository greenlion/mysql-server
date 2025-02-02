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

PSQL="/usr/bin/psql -e -d $SID -c"

if [ ${USE_TABLESPACES} -eq 1 ];then
	TS_PK_SUPPLIER_DIR="${TSDIR}/pk_supplier/ts"
	TS_PK_PART_DIR="${TSDIR}/pk_part/ts"
	TS_PK_PARTSUPP_DIR="${TSDIR}/pk_partsupp/ts"
	TS_PK_CUSTOMER_DIR="${TSDIR}/pk_customer/ts"
	TS_PK_ORDERS_DIR="${TSDIR}/pk_orders/ts"
	TS_PK_LINEITEM_DIR="${TSDIR}/pk_lineitem/ts"
	TS_PK_NATION_DIR="${TSDIR}/pk_nation/ts"
	TS_PK_REGION_DIR="${TSDIR}/pk_region/ts"

	TS_I_L_SHIPDATE_DIR="${TSDIR}/i_l_shipdate/ts"
	TS_I_L_SUPPKEY_PARTKEY_DIR="${TSDIR}/i_l_suppkey_partkey/ts"
	TS_I_L_PARTKEY_DIR="${TSDIR}/i_l_partkey/ts"
	TS_I_L_SUPPKEY_DIR="${TSDIR}/i_l_suppkey/ts"
	TS_I_L_RECEIPTDATE_DIR="${TSDIR}/i_l_receiptdate/ts"
	TS_I_L_ORDERKEY_DIR="${TSDIR}/i_l_orderkey/ts"
	TS_I_L_ORDERKEY_QUANTITY_DIR="${TSDIR}/i_l_orderkey_quantity/ts"
	TS_I_C_NATIONKEY_DIR="${TSDIR}/i_c_nationkey/ts"
	TS_I_O_ORDERDATE_DIR="${TSDIR}/i_o_orderdate/ts"
	TS_I_O_CUSTKEY_DIR="${TSDIR}/i_o_custkey/ts"
	TS_I_S_NATIONKEY_DIR="${TSDIR}/i_s_nationkey/ts"
	TS_I_PS_PARTKEY_DIR="${TSDIR}/i_ps_partkey/ts"
	TS_I_PS_SUPPKEY_DIR="${TSDIR}/i_ps_suppkey/ts"
	TS_I_N_REGIONKEY_DIR="${TSDIR}/i_n_regionkey/ts"
	TS_I_L_COMMITDATE_DIR="${TSDIR}/i_l_commitdate/ts"

	mkdir -p ${TS_PK_SUPPLIER_DIR}
	mkdir -p ${TS_PK_PART_DIR}
	mkdir -p ${TS_PK_PARTSUPP_DIR}
	mkdir -p ${TS_PK_CUSTOMER_DIR}
	mkdir -p ${TS_PK_ORDERS_DIR}
	mkdir -p ${TS_PK_LINEITEM_DIR}
	mkdir -p ${TS_PK_NATION_DIR}
	mkdir -p ${TS_PK_REGION_DIR}

	mkdir -p ${TS_I_L_SHIPDATE_DIR}
	mkdir -p ${TS_I_L_SUPPKEY_PARTKEY_DIR}
	mkdir -p ${TS_I_L_PARTKEY_DIR}
	mkdir -p ${TS_I_L_SUPPKEY_DIR}
	mkdir -p ${TS_I_L_RECEIPTDATE_DIR}
	mkdir -p ${TS_I_L_ORDERKEY_DIR}
	mkdir -p ${TS_I_L_ORDERKEY_QUANTITY_DIR}
	mkdir -p ${TS_I_C_NATIONKEY_DIR}
	mkdir -p ${TS_I_O_ORDERDATE_DIR}
	mkdir -p ${TS_I_O_CUSTKEY_DIR}
	mkdir -p ${TS_I_S_NATIONKEY_DIR}
	mkdir -p ${TS_I_PS_PARTKEY_DIR}
	mkdir -p ${TS_I_PS_SUPPKEY_DIR}
	mkdir -p ${TS_I_N_REGIONKEY_DIR}
	mkdir -p ${TS_I_L_COMMITDATE_DIR}

	TS_PK_SUPPLIER="TABLESPACE dbt3_pk_supplier"
	TS_PK_PART="TABLESPACE dbt3_pk_part"
	TS_PK_PARTSUPP="TABLESPACE dbt3_pk_partsupp"
	TS_PK_CUSTOMER="TABLESPACE dbt3_pk_customer"
	TS_PK_ORDERS="TABLESPACE dbt3_pk_orders"
	TS_PK_LINEITEM="TABLESPACE dbt3_pk_lineitem"
	TS_PK_NATION="TABLESPACE dbt3_pk_nation"
	TS_PK_REGION="TABLESPACE dbt3_pk_region"

	TS_I_L_SHIPDATE="TABLESPACE dbt3_i_l_shipdate"
	TS_I_L_SUPPKEY_PARTKEY="TABLESPACE dbt3_i_l_suppkey_partkey"
	TS_I_L_PARTKEY="TABLESPACE dbt3_i_l_partkey"
	TS_I_L_SUPPKEY="TABLESPACE dbt3_i_l_suppkey"
	TS_I_L_RECEIPTDATE="TABLESPACE dbt3_i_l_receiptdate"
	TS_I_L_ORDERKEY="TABLESPACE dbt3_i_l_orderkey"
	TS_I_L_ORDERKEY_QUANTITY="TABLESPACE dbt3_i_l_orderkey_quantity"
	TS_I_C_NATIONKEY="TABLESPACE dbt3_i_c_nationkey"
	TS_I_O_ORDERDATE="TABLESPACE dbt3_i_o_orderdate"
	TS_I_O_CUSTKEY="TABLESPACE dbt3_i_o_custkey"
	TS_I_S_NATIONKEY="TABLESPACE dbt3_i_s_nationkey"
	TS_I_PS_PARTKEY="TABLESPACE dbt3_i_ps_partkey"
	TS_I_PS_SUPPKEY="TABLESPACE dbt3_i_ps_suppkey"
	TS_I_N_REGIONKEY="TABLESPACE dbt3_i_n_regionkey"
	TS_I_L_COMMITDATE="TABLESPACE dbt3_i_l_commitdate"

	${PSQL} "CREATE ${TS_PK_SUPPLIER} LOCATION '${TS_PK_SUPPLIER_DIR}'";
	${PSQL} "CREATE ${TS_PK_PART} LOCATION '${TS_PK_PART_DIR}'";
	${PSQL} "CREATE ${TS_PK_PARTSUPP} LOCATION '${TS_PK_PARTSUPP_DIR}'";
	${PSQL} "CREATE ${TS_PK_CUSTOMER} LOCATION '${TS_PK_CUSTOMER_DIR}'";
	${PSQL} "CREATE ${TS_PK_ORDERS} LOCATION '${TS_PK_ORDERS_DIR}'";
	${PSQL} "CREATE ${TS_PK_LINEITEM} LOCATION '${TS_PK_LINEITEM_DIR}'";
	${PSQL} "CREATE ${TS_PK_NATION} LOCATION '${TS_PK_NATION_DIR}'";
	${PSQL} "CREATE ${TS_PK_REGION} LOCATION '${TS_PK_REGION_DIR}'";

	${PSQL} "CREATE ${TS_I_L_SHIPDATE} LOCATION '${TS_I_L_SHIPDATE_DIR}'";
	${PSQL} "CREATE ${TS_I_L_SUPPKEY_PARTKEY} LOCATION '${TS_I_L_SUPPKEY_PARTKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_L_PARTKEY} LOCATION '${TS_I_L_PARTKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_L_SUPPKEY} LOCATION '${TS_I_L_SUPPKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_L_RECEIPTDATE} LOCATION '${TS_I_L_RECEIPTDATE_DIR}'";
	${PSQL} "CREATE ${TS_I_L_ORDERKEY} LOCATION '${TS_I_L_ORDERKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_L_ORDERKEY_QUANTITY} LOCATION '${TS_I_L_ORDERKEY_QUANTITY_DIR}'";
	${PSQL} "CREATE ${TS_I_C_NATIONKEY} LOCATION '${TS_I_C_NATIONKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_O_ORDERDATE} LOCATION '${TS_I_O_ORDERDATE_DIR}'";
	${PSQL} "CREATE ${TS_I_O_CUSTKEY} LOCATION '${TS_I_O_CUSTKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_S_NATIONKEY} LOCATION '${TS_I_S_NATIONKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_PS_PARTKEY} LOCATION '${TS_I_PS_PARTKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_PS_SUPPKEY} LOCATION '${TS_I_PS_SUPPKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_N_REGIONKEY} LOCATION '${TS_I_N_REGIONKEY_DIR}'";
	${PSQL} "CREATE ${TS_I_L_COMMITDATE} LOCATION '${TS_I_L_COMMITDATE_DIR}'";

	TS_PK_SUPPLIER="USING INDEX ${TS_PK_SUPPLIER}"
	TS_PK_PART="USING INDEX ${TS_PK_PART}"
	TS_PK_PARTSUPP="USING INDEX ${TS_PK_PARTSUPP}"
	TS_PK_CUSTOMER="USING INDEX ${TS_PK_CUSTOMER}"
	TS_PK_ORDERS="USING INDEX ${TS_PK_ORDERS}"
	TS_PK_LINEITEM="USING INDEX ${TS_PK_LINEITEM}"
	TS_PK_NATION="USING INDEX ${TS_PK_NATION}"
	TS_PK_REGION="USING INDEX ${TS_PK_REGION}"
fi

echo "Creating indexes..."

${PSQL} "
ALTER TABLE supplier
ADD CONSTRAINT pk_supplier PRIMARY KEY (s_suppkey) ${TS_PK_SUPPLIER};
" || exit 1 &

${PSQL} "
ALTER TABLE part
ADD CONSTRAINT pk_part PRIMARY KEY (p_partkey) ${TS_PK_PART};
" || exit 1 &

${PSQL} "
ALTER TABLE partsupp
ADD CONSTRAINT pk_partsupp PRIMARY KEY (ps_partkey, ps_suppkey) ${TS_PK_PARTSUPP};
" || exit 1 &

${PSQL} "
ALTER TABLE customer
ADD CONSTRAINT pk_customer PRIMARY KEY (c_custkey) ${TS_PK_CUSTOMER};
" || exit 1 &

${PSQL} "
ALTER TABLE orders
ADD CONSTRAINT pk_orders PRIMARY KEY (o_orderkey) ${TS_PK_ORDERS};
" || exit 1 &

${PSQL} "
ALTER TABLE lineitem
ADD CONSTRAINT pk_lineitem PRIMARY KEY (l_orderkey, l_linenumber) ${TS_PK_LINEITEM};
" || exit 1 &

${PSQL} "
ALTER TABLE nation
ADD CONSTRAINT pk_nation PRIMARY KEY (n_nationkey) ${TS_PK_NATION};
" || exit 1 &

${PSQL} "
ALTER TABLE region
ADD CONSTRAINT pk_region PRIMARY KEY (r_regionkey) ${TS_PK_REGION};
" || exit 1 &

${PSQL} "
CREATE INDEX i_l_shipdate
ON lineitem (l_shipdate) ${TS_I_L_SHIPDATE};
" || exit 1  &

${PSQL} "
CREATE INDEX i_l_suppkey_partkey
ON lineitem (l_partkey, l_suppkey) ${TS_I_L_SUPPKEY_PARTKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_l_partkey
ON lineitem (l_partkey) ${TS_I_L_PARTKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_l_suppkey
ON lineitem (l_suppkey) ${TS_I_L_SUPPKEY};
" || exit 1 &
${PSQL} "
CREATE INDEX i_l_receiptdate
ON lineitem (l_receiptdate) ${TS_I_L_RECEIPTDATE};
" || exit 1 &

${PSQL} "
CREATE INDEX i_l_orderkey
ON lineitem (l_orderkey) ${TS_I_L_ORDERKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_l_orderkey_quantity
ON lineitem (l_orderkey, l_quantity) ${TS_I_L_ORDERKEY_QUANTITY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_c_nationkey
ON customer (c_nationkey) ${TS_I_C_NATIONKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_o_orderdate
ON orders (o_orderdate) ${TS_I_O_ORDERDATE};
" || exit 1 &

${PSQL} "
CREATE INDEX i_o_custkey
ON orders (o_custkey) ${TS_I_O_CUSTKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_s_nationkey
ON supplier (s_nationkey) ${TS_I_S_NATIONKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_ps_partkey
ON partsupp (ps_partkey) ${TS_I_PS_PARTKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_ps_suppkey
ON partsupp (ps_suppkey) ${TS_I_PS_SUPPKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_n_regionkey
ON nation (n_regionkey) ${TS_I_N_REGIONKEY};
" || exit 1 &

${PSQL} "
CREATE INDEX i_l_commitdate
ON lineitem (l_commitdate) ${TS_I_L_COMMITDATE};
" || exit 1 &

wait

exit 0
