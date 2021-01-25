#!/bin/sh

if which gmake 2> /dev/null
then
	make=gmake
else
	make=make
fi
pwd=`pwd`
bak=~/NaTT.backup
tar="tar"

doc="README.txt"
bin="NaTT.exe"
script="NaTT.sh xtc2tpdb.xml"
src="*.ml *.mll *.mly Makefile"

if [ "$1" = "-s" ]
then
	shift
	starexec=y
else
	starexec=n
fi

chmod -x $src $common

if [ -e "$bak" ]
then
	if [ -e "$bak/$1.tar.gz" ]
	then
		echo Please specify other name!
		exit 1
	fi
	
	$make || exit 1
	
	mkdir "$bak/NaTT"
	mkdir "$bak/NaTT/bin"

    eval cp $doc $src \"$bak/NaTT\"
    eval cp $bin $script \"$bak/NaTT/bin\"

	(cd $bak; $tar -czf $1.tar.gz NaTT)
	
	if [ "$starexec" = "y" ]
	then
		rm -rf "$bak/NaTT"
		eval cp $bin $script starexec_* \"$bak/NaTT/bin\"
		(cd $bak; $tar -czf $1.starexec.tar.gz NaTT)
	fi
	
	rm -rf "$bak/NaTT"
else
	echo Please make directory "$bak"!
	exit 1
fi
