#!/bin/sh

dir=${0%/*}
options=
proof=
ext=xml
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

pre="/usr/bin/time -p -o $timefile timeout $t $dir/NaTT.exe"

l=$1
shift

if [ -e $l/all.list ]
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
			(cd "$d"; find -type f -name "*.$ext") |
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
		log=/dev/stderr
	else
		log="${f%.trs}.txt"
		log="$proof/${log//\//-}"
	fi
	if [ "${f##*.}" = "xml" ]
	then
		out=`eval xsltproc "$dir/xtc2tpdb.xml" "$d$f" | $pre "$@" $options 2> "$log"`
	else
		out=`eval $pre "$d$f" "$@" $options 2> "$log"`
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

