#!/bin/sh

#
# This file is released under the terms of the Artistic License.
# Please see the file LICENSE, included in this package, for details.
#
# Copyright (C) 2005 Mark Wong & Open Source Development Lab, Inc.
#

DIR=`dirname $0`
. ${DIR}/pgsql_profile || exit 1

if [ -f ${PGDATA}/postmaster.pid ]; then
	echo "Database is already started."
	exit 0
fi

LOGFILE="log"
USE_PG_AUTOVACUUM=0
OUTDIR="."
while getopts "ao:p:" OPT; do
	case ${OPT} in
	a)
		USE_PG_AUTOVACUUM=1
		;;
	o)
		OUTDIR=${OPTARG}
		;;
	p)
		PARAMETERS=${OPTARG}
		;;
	esac
done

CMD="/usr/lib/postgresql/12/bin//pg_ctl -D ${PGDATA} start -l ${OUTDIR}/log.txt"
if [ "${PARAMETERS}" = "" ]; then
	${CMD} || exit 1
else
	${CMD} -o "${PARAMETERS}" || exit 1
fi

sleep 10

exit 0
