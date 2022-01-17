#!/bin/sh

if which gmake
then
	make=gmake
else
	make=make
fi
pwd=`pwd`
bak=~/NaTT.backup
tar="tar"

src="README.md *.ml *.mll *.mly Makefile"
scripts="xtc2tpdb.xsl NaTT.sh"
bin="NaTT.exe"

if [ "$1" = "-r" ]
then
	shift
	release=y
else
	release=n
fi

chmod -x $src

if [ -e "$bak" ]
then
	if [ -e "$bak/$1.tar.gz" ]
	then
		echo Please specify other name!
		exit 1
	fi
	mkdir $bak/NaTT $bak/NaTT/bin
	cp $src "$bak/NaTT"
	cd bin
	cp $scripts "$bak/NaTT/bin"
	cd "$bak"
	$tar -czf $1.tar.gz NaTT
	(cd NaTT; $make) || exit 1
	rm -rf NaTT
else
	echo Please make directory "$bak"!
	exit 1
fi
