#!/bin/sh

dir=${0%/*}
options=
proof=
timefile="$dir/tmp.time"

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
		echo -n "$@: " 1>&2
	}
	options="$options $1"
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

pre="/usr/bin/time -p -o $timefile timeout $t $dir/NaTT"

l=$1
shift

if [ -e $l/all.list ]
then
	l=$l/all.list
fi

if [ "${l##*.}" = "list" ]
then
	d=${l%/*}/
	info "----------------------------------"
	info "  $d  "
	info "----------------------------------"
else
	d=
fi

(	if [ "${l##*.}" = "list" ]
	then
		cat "$l"
	else
		if [ -d "$l" ]
		then
			find "$l" -type f -name "*.trs"
		else
			echo "$l"
		fi
	fi
) |
while read f
do
	finfo "$f"
#	read dummy < /dev/tty
	if [ "$proof" = "" ]
	then
		post=
	else
		post="2> $proof/${f##*/trs/}.txt"
	fi
	if [ "${f##*.}" = "xml" ]
	then
		out=`eval xsltproc "$dir/xtc2tpdb.xml" "$d$f" | $pre "$@" $options $post`
	else
		out=`eval $pre "$d$f" "$@" $options $post`
	fi
	if [ "$out" = "" -o "$out" = "Killed" ]
	then
		echo -n "TIMEOUT	"
	else
		echo -n "$out	"
	fi
	sed -e "/real/s/real[ 	]*//;q" $timefile
	rm -f $timefile
done

