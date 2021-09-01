#!/bin/bash

if which gmake 2> /dev/null
then
	make=gmake
else
	make=make
fi
pwd=`pwd`
bak=~/NaTT.backup
tar="tar"

doc="README.md"
bin="NaTT.exe NaTT.sh *.xml"

if [ -e "$bak" ]
then
	if [ -e "$bak/$1.tar.gz" ]
	then
		echo Please specify other name!
		exit 1
	fi
	
	$make || exit 1
	
	mkdir "$bak/bin"
	cp $doc $bak

	(cd bin; eval cp $bin starexec_* z3 \"$bak/bin/\")

	(cd $bak; $tar -czf $1.tar.gz bin $doc)
	
	rm -rf "$bak/bin" $bak/$doc
else
	echo Please make directory "$bak"!
	exit 1
fi
