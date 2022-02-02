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
bin="NaTT.exe NaTT.sh z3 txtr-0.jar trs.xml.txtr"

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
	cp -r strategies $bak

	(cd bin; eval cp $bin starexec_* \"$bak/bin/\")

	(cd $bak; $tar -czf $1.tar.gz bin $doc strategies)
	
	rm -rf "$bak/bin" $bak/$doc
else
	echo Please make directory "$bak"!
	exit 1
fi
