#!/bin/bash

#
# This file is released under the terms of the Artistic License.  Please see
# the file LICENSE, included in this package, for details.
#
# Copyright (C) 2002 Open Source Development Lab, Inc.
# History:
# June-4-2003 Create by Jenny Zhang

. /home/justin/warp/storage/warp/benchmark/dbt3-1.9/scripts/dbt3_profile || exit 1

USE_TABLESPACES=0
while getopts "t" OPT; do
	case ${OPT} in
	t)
		USE_TABLESPACES=1
		;;
	esac
done

echo "Loading table tables... "

PSQL="/usr/bin/psql -e -d $SID -c"

date
if [ ${USE_TABLESPACES} -eq 1 ]; then
	${PSQL} "COPY supplier FROM '$DSS_PATH/supplier.tbl' USING DELIMITERS '|';" || exit 1 &
	${PSQL} "COPY part FROM '$DSS_PATH/part.tbl' USING DELIMITERS '|';" || exit 1 &
	${PSQL} "COPY partsupp FROM '$DSS_PATH/partsupp.tbl' USING DELIMITERS '|';" || exit 1 &
	${PSQL} "COPY customer FROM '$DSS_PATH/customer.tbl' USING DELIMITERS '|';" || exit 1 &
	${PSQL} "COPY orders FROM '$DSS_PATH/orders.tbl' USING DELIMITERS '|';" || exit 1 &
	${PSQL} "COPY lineitem FROM '$DSS_PATH/lineitem.tbl' USING DELIMITERS '|';" || exit 1 &
	${PSQL} "COPY nation FROM '$DSS_PATH/nation.tbl' USING DELIMITERS '|';" || exit 1 &
	${PSQL} "COPY region FROM '$DSS_PATH/region.tbl' USING DELIMITERS '|';" || exit 1 &
else
	${PSQL} "COPY supplier FROM '$DSS_PATH/supplier.tbl' USING DELIMITERS '|';" || exit 1
	${PSQL} "COPY part FROM '$DSS_PATH/part.tbl' USING DELIMITERS '|';" || exit 1
	${PSQL} "COPY partsupp FROM '$DSS_PATH/partsupp.tbl' USING DELIMITERS '|';" || exit 1
	${PSQL} "COPY customer FROM '$DSS_PATH/customer.tbl' USING DELIMITERS '|';" || exit 1
	${PSQL} "COPY orders FROM '$DSS_PATH/orders.tbl' USING DELIMITERS '|';" || exit 1
	${PSQL} "COPY lineitem FROM '$DSS_PATH/lineitem.tbl' USING DELIMITERS '|';" || exit 1
	${PSQL} "COPY nation FROM '$DSS_PATH/nation.tbl' USING DELIMITERS '|';" || exit 1
	${PSQL} "COPY region FROM '$DSS_PATH/region.tbl' USING DELIMITERS '|';" || exit 1
fi

wait

exit 0
