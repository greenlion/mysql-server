#!/bin/bash

DIR=`dirname $0`
. ${DIR}/dbt3_profile || exit 1

if [ $# -ne 1 ]; then
	echo "usage: gen_html.sh <results directory>"
fi

DIR=$1

SRCDIR=/home/justin/warp/storage/warp/benchmark/dbt3-1.9
DBDIR=pgsql

OSVER=`uname -s -r`
DBVER=`${SHELL} $DBDIR/get_version.sh`

CPU_MODEL=`uname -p`
CPUS=`grep CPUS ${DIR}/config.txt | awk '{print $2}'`
CPU_MHZ=`grep MHz ${DIR}/config.txt | awk '{print $2}'`
RAM=`grep memory ${DIR}/config.txt | awk '{print $2}'`

SF=`grep scale_factor ${DIR}/config.txt | awk '{print $2}'`
STREAMS=`grep num_stream ${DIR}/config.txt | awk '{print $2}'`

LOAD=`grep LOAD ${DIR}/q_time.out | awk '{ print $11 }'`
# Round to 2 decimal places, convert to hours.
LOAD=`echo "scale=2; ${LOAD} / 3600" | bc -l`
COMPOSITE=`grep composite ${DIR}/calc_composite.out | awk '{print $3}'`
POWER=`grep power ${DIR}/calc_composite.out | awk '{print $3}'`
THROUGHPUT=`grep throughput ${DIR}/calc_composite.out | awk '{print $3}'`

gen_results()
{
	SUBDIR=$2

	echo "<html>" > ${SUBDIR}/index.html
	echo "<head>" >> ${SUBDIR}/index.html
	echo "<title>Database Test 3 $1 Results</title>" >> ${SUBDIR}/index.html
	echo "</head>" >> ${SUBDIR}/index.html
	echo "<body>" >> ${SUBDIR}/index.html

	echo "<img src=\"plots/cpu.png\" />" >> ${SUBDIR}/index.html
	echo "<p>" >> ${SUBDIR}/index.html
	echo "</p>" >> ${SUBDIR}/index.html

	# Create HTML page for chargs.
	echo "<html>" > ${SUBDIR}/vmcharts.html
	echo "<head>" >> ${SUBDIR}/vmcharts.html
	echo "<title>Database Test 3 $1 Result vmstat Charts</title>" >> ${SUBDIR}/vmcharts.html
	echo "</head>" >> ${SUBDIR}/vmcharts.html
	echo "<body>" >> ${SUBDIR}/vmcharts.html
	echo "<img src=\"plots/cpu.png\" /><br />" >> ${SUBDIR}/vmcharts.html
	echo "<hr />" >> ${SUBDIR}/vmcharts.html
	echo "<img src=\"plots/cs.png\" /><br />" >> ${SUBDIR}/vmcharts.html
	echo "<hr />" >> ${SUBDIR}/vmcharts.html
	echo "<img src=\"plots/in.png\" /><br />" >> ${SUBDIR}/vmcharts.html
	echo "<hr />" >> ${SUBDIR}/vmcharts.html
	echo "<img src=\"plots/io.png\" /><br />" >> ${SUBDIR}/vmcharts.html
	echo "<hr />" >> ${SUBDIR}/vmcharts.html
	echo "<img src=\"plots/memory.png\" /><br />" >> ${SUBDIR}/vmcharts.html
	echo "<hr />" >> ${SUBDIR}/vmcharts.html
	echo "<img src=\"plots/procs.png\" /><br />" >> ${SUBDIR}/vmcharts.html
	echo "<hr />" >> ${SUBDIR}/vmcharts.html
	echo "<img src=\"plots/swap.png\" /><br />" >> ${SUBDIR}/vmcharts.html
	echo "</body>" >> ${SUBDIR}/vmcharts.html
	echo "</html>" >> ${SUBDIR}/vmcharts.html


	echo "<h2>System Statistics</h2>" >> ${SUBDIR}/index.html
	echo "<a href=\"sar.txt\">sar</a><br />" >> ${SUBDIR}/index.html
	echo "<a href=\"vmstat.out\">vmstat</a> [<a href=\"vmcharts.html\">charts</a>]<br />" >> ${SUBDIR}/index.html
	echo "<a href=\"iostatx.out\">iostat</a><br />" >> ${SUBDIR}/index.html
	echo "<a href=\"ipcs.out\">ipcs</a><br />" >> ${SUBDIR}/index.html

	echo "<h2>Kernel and Application Profiles</h2>" >> ${SUBDIR}/index.html
	echo "<p>"
	if [ -f "${SUBDIR}/readprofile.txt" ]; then
		echo "<a href=\"readprofile.txt\">readprofile</a><br />" >> ${SUBDIR}/index.html
	fi
	if [ -d "${SUBDIR}/oprofile" ]; then
		echo "<a href=\"oprofile/oprofile.txt\">oprofile</a><br />" >> ${SUBDIR}/index.html
		echo "<a href=\"oprofile/assembly.txt\">annotated assembly</a><br />" >> ${SUBDIR}/index.html
	fi
	echo "</p>" >> ${SUBDIR}/index.html

	echo "<h2>Database Information</h2>" >> ${SUBDIR}/index.html
	echo "<a href=\"param.out\">database parameters</a><br />" >> ${SUBDIR}/index.html
	echo "<a href=\"db/\">database raw statistics</a> [<a href=\"db.html\">charts</a>]<br />" >> ${SUBDIR}/index.html
	if [ "$1" != "Load Test" ]; then
		echo "<a href=\"db/indexes.out\">table indexes</a><br />" >> ${SUBDIR}/index.html
		echo "<a href=\"db/plans\">query plans</a><br />" >> ${SUBDIR}/index.html
		echo "<a href=\"results\">query results</a><br />" >> ${SUBDIR}/index.html
	fi

	echo "</body>" >> ${SUBDIR}/index.html
	echo "</html>" >> ${SUBDIR}/index.html

	# Database Charts
	echo "<html>" > ${SUBDIR}/db.html
	echo "<head>" >> ${SUBDIR}/db.html
	echo "<title>Database Test 3 $1 Database Charts</title>" >> ${SUBDIR}/db.html
	echo "</head>" >> ${SUBDIR}/db.html
	echo "<body>" >> ${SUBDIR}/db.html
	echo "Index Scans<br/>" >> ${SUBDIR}/db.html
	echo "<img src=\"db/indexes_scan.png\" />" >> ${SUBDIR}/db.html

	echo "<hr/>" >> ${SUBDIR}/db.html

	echo "Index Blocks Read<br/>" >> ${SUBDIR}/db.html
	echo "<img src=\"db/index_info.png\" />" >> ${SUBDIR}/db.html

	echo "<hr/>" >> ${SUBDIR}/db.html

	echo "Table Blocks Read<br/>" >> ${SUBDIR}/db.html
	echo "<img src=\"db/table_info.png\" />" >> ${SUBDIR}/db.html
	echo "</body>" >> ${SUBDIR}/db.html
	echo "</html>" >> ${SUBDIR}/db.html

	${SHELL} $SRCDIR/scripts/vmplot.sh -i ${SUBDIR}/vmstat.out -o ${SUBDIR}/plots -x "Minutes" > /dev/null 2>&1
	perl $SRCDIR/scripts/${DBDIR}/analyze_stats.pl --dir ${SUBDIR}/db > /dev/null 2>&1
}

echo "<html>"
echo "<head>"
echo "<title>Database Test 3 Results</title>"
echo "</head>"
echo "<body>"
echo "<h1>Database Test 3 Results</h1>"

echo "<table border=\"1\">"
echo "<tr>"
echo "<th>Software Version</th><th>Hardware Configuration</th><th>Workload Parameters</th>"
echo "</tr>"
echo "<tr>"
echo "<td>Operating System: ${OSVER}</td><td>${CPUS} CPUs @ ${CPU_MHZ}</td><td>Scale Factor: ${SF}</td>"
echo "</tr>"
echo "<tr>"
echo "<td>Database Server: ${DBVER}</td><td>${CPU_MODEL}</td><td>Streams: ${STREAMS}</td>"
echo "</tr>"
echo "<tr>"
echo "<td></td><td>${RAM} KB RAM</td><td></td>"
echo "</tr>"
echo "</table>"

echo "<h2>Metrics</h2>"
echo "<table border=\"0\">"
echo "<tr>"
echo "<td align=\"right\">Composite:</td><td align=\"right\">${COMPOSITE}</td>"
echo "</tr>"
echo "<tr>"
echo "<td align=\"right\">Load Time:</td><td align=\"right\">${LOAD} Hours</td>"
echo "</tr>"
echo "<tr>"
echo "<td align=\"right\">Query Processing Power:</td><td align=\"right\">${POWER}</td>"
echo "</tr>"
echo "<tr>"
echo "<td align=\"right\">Throughput Numerical Quantity:</td><td align=\"right\">${THROUGHPUT}</td>"
echo "</tr>"
echo "</table>"

echo "<h2>Query Times</h2>"
echo "<img src=\"q_time.png\" />"
echo "<p>"
echo "<a href=\"q_time.out\">Text Version of Chart</a>"
echo "</p>"

# Generate individual Web pages for each test result directory.
echo "<h2>Individual Test Results</h2>"

cd ${DIR}

# There will always only be 1 load test.
gen_results "Load Test" "load"
echo "<p>"
echo "<a href=\"load\">Load Test</a>"
echo "</p>"

echo "<p>"
i=1
for ARG in `ls -d power*`
do
	gen_results "Power Test" $ARG
	echo "<a href=\"$ARG\">Power Test ${i}</a>"
	let "i=$i+1"
done
echo "</p>"

echo "<p>"
i=1
for ARG in `ls -d throughput*`
do
	gen_results "Throughput Test" $ARG
	echo "<a href=\"$ARG\">Throughput Test ${i}</a>"
	let "i=$i+1"
done
echo "</p>"

echo "</body>"
echo "</html>"
