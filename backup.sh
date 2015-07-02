#!/bin/sh

pwd=`pwd`
bak=~/NaTT.backup
tar="tar"

common="README.txt xtc2tpdb.xml"
bin="NaTT.exe"
script="NaTT.sh"
src="*.ml *.mll *.mly Makefile"
local="$common $script $src *.sh *.mk"

if [ "$1" = "-r" ]
then
	shift
	release=y
else
	release=n
fi

chmod -x $src $common

if [ -e "$bak" ]
then
	if [ -e "$bak/$1.tar.gz" ]
	then
		echo Please specify other name!
		exit 1
	fi
	
	make || exit 1
	
	cd "$bak"
	
	mkdir NaTT
	
	(cd "$pwd"; eval cp $local \"$bak/NaTT\")
	$tar -czf $1.tar.gz NaTT
	
	if [ "$release" = "y" ]
	then
		rm -f NaTT/*
		(cd "$pwd"; echo cp $bin $script $common \"$bak/NaTT\")
		$tar -czf $1.bin.tar.gz NaTT
		rm -f NaTT/*
		(cd "$pwd"; eval cp $src $script $common \"$bak/NaTT\")
		$tar -czf $1.src.tar.gz NaTT
	fi
	
	rm -rf NaTT
else
	echo Please make directory "$bak"!
	exit 1
fi
