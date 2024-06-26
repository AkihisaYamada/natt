#!/bin/bash

dir=${0%/*}
options=
proof=
ext=ari

info()
{
	echo "$@" 1>&2
}
finfo()
{
	info "======== $@ ========"
}

if [ "$1" = "-V" ]
then
	info()
	{
		:
	}
	finfo()
	{
		echo -n "$@: "
	}
	options="$options $1"
	shift
fi

if [ "$1" = "-trs" ]
then
	ext="trs"
	shift
fi

if [ "${1%:*}" = "-T" ]
then
	t="${1##*:}"
	shift
else
	t=60
fi

if [ "${1%:*}" = "-p" ]
then
	info()
	{
		:
	}
	proof="${1#-p:}"
	shift
fi

if [ "${1%:*}" = "-x" ]
then
	info()
	{
		:
	}
	options="$options -V"
	cpfdir="${1#-x:}"
	shift
fi

l=$1
shift

if [ -d "$l" -a -e "$l/all.list" ]
then
	l=$l/all.list
fi

if [ "${l##*.}" = "list" ]
then
	d="${l%/*}/"
else
	if [ -d "$l" ]
	then
		d="$l/"
		l=
	else
		d=
	fi
fi

if [ "" != "$d" ]
then
	info "----------------------------------"
	info "  $d  "
	info "----------------------------------"
fi

(	if [ "${l##*.}" = "list" ]
	then
		cat "$l"
	else
		if [ "$d" = "" ]
		then
			echo "$l"
		else
			(cd "$d"; find . -type f -name "*.$ext") |
			sed -e "s/^\.\///g"
		fi
	fi
) |
while read f
do
	finfo "$f"
#	read dummy < /dev/tty
	if [ "$proof" = "" ]
	then
		log="/dev/stdout"
	else
		log="${f%.*}.txt"
		log="$proof/${log//\//-}"
	fi
	if [ "$cpfdir" = "" ]
	then
		cpffile=
	else
		cpffile="${f%.*}.xml"
		cpffile="$cpfdir/${cpffile//\//-}"
		cpfopt=-x:"$cpffile"
	fi
	timefile=`mktemp`
	outfile=`mktemp`
	if [ "${f##*.}" = "xml" ]
	then
		cat "$d$f"
	else
		java -jar "$dir/txtr-0.jar" "$dir/ari.xml.txtr" "$d$f"
	fi | {
		time -p {
			timeout $t "$dir/NaTT.exe" $cpfopt "$@" $options 1> "$outfile"
		} 2> "$log"
	} 2> "$timefile"
	out=`sed -E "s/([A-Z]+)/\1/;q" "$outfile"`
	if [ "$out" = "" -o "$out" = "Killed" ]
	then
		echo -n "TIMEOUT	"
	else
		echo -n "$out	"
	fi
	sed -E "s/real[ 	]*([0-9.]+).+$/\1/;q" $timefile
	rm -f $timefile $outfile
	if [ "$ceta" != "" -a "$cpffile" != "" -a "$out" = "YES" ]
	then
		"$ceta" "$cpffile"
	fi
done

