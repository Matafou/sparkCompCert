#!/bin/bash
# Example:
#./configure.sh -compcert ~/work/CompCert-official -spark ~/work/sparkformal/spark2014_semantics/src
#

function usage {
    echo
    echo usage:  configure.sh [-coqtags bin] [-compcert path] [-spark path] [-sireum path]
    echo 

    echo "  builds the _CoqProject and makefile (coq_makefile -f _CoqProject) of the"
    echo "  project amended with a specific \"tags\" target and adapted to the paths"
    echo "  given in arguments."
    echo "  NOTE: coq_makefile generates a warning about compcert directory not"
    echo "    being a subdirectory. Don't pay attention."
}
for i in $*; do
    case $i in
	"-h") usage; exit 0;;
    esac
done

# to echo commands before executing them:
exe() { echo "\$ $@" ; "$@" ; }

# Getting the directory containing the current script and also the
# config file, which has default values for arguments
resourcedir=${0%/*}

# loading defaults
. $resourcedir/Config/config.in

# loading path given explicitely by the user
for i in $*; do
    case $i in
	"-coqtags") FOUNDCOQTAGS=yes;;
	"-spark") FOUNDSPARK=yes;;
	"-compcert") FOUNDCOMPCERT=yes;;
	"-sireum") SIREUM=yes;;
	*)
	    if [[ $FOUNDCOQTAGS == yes ]] ;
	    then
		COQTAGS=$i
		FOUNDCOQTAGS=finished;
	    else if [[ $FOUNDSPARK == yes ]] ;
	    then
		SPARK=$i
		FOUNDSPARK=finished;
	    else if [[ $FOUNDCOMPCERT == yes ]] ;
	    then
		COMPCERT=$i
		FOUNDCOMPCERT=finished;
	    else if [[ $SIREUM == yes ]] ;
	    then
		SIREUM=$i
		FOUNDSIREUM=finished;
	    fi
	    fi
	    fi
	    fi ;;
    esac
done

# storing the configuration in a file
> $resourcedir/.config

echo COQTAGS=$COQTAGS >> $resourcedir/.config
echo COMPCERT=$COMPCERT >> $resourcedir/.config
echo SPARK=$SPARK >> $resourcedir/.config
echo SIREUM=$SIREUM >> $resourcedir/.config

# Generate the _CoqProject file
echo "### PROJECT FILE GENERATED AUTOMATICALLY by configure.sh" > _CoqProject
echo "### you can pass options to configure.sh (see configure.sh -h)"  >> _CoqProject
echo "### FIRST PART: copied from Config/_CoqProject.in, altered by"  >> _CoqProject
echo "### options given to configure.sh"  >> _CoqProject

cat < $resourcedir/Config/_CoqProject.in >> ./_CoqProject
sed --posix -e "s%@COMPCERT%$COMPCERT%" ./_CoqProject | sponge ./_CoqProject
sed --posix -e "s%@SPARK%$SPARK%" ./_CoqProject | sponge ./_CoqProject


echo "Options set in _CoqProject files:"
echo "***************************"
cat < _CoqProject | grep -v "#"
echo "***************************"

echo "" >> _CoqProject
echo "### SECOND PART: Files added automatically by configure.sh." >> _CoqProject

ls -1 *.v >> _CoqProject 

# find $resourcedir/sparktests -name "*svn*" -prune -o -name "language_template\.v" -prune -o \( -name "*\.v" -print \) >>  ./_CoqProject

# Generate the Makefile from _CoqProject + add a coqtags target
coq_makefile -install none -f _CoqProject -o Makefile 
# clean would clean Compcert, let us rename the target
# no more compcert target now:
# sed --posix -e "s/clean:/superclean:/" ./Makefile | sponge ./Makefile



echo "
# ADDED BY build_make.sh:

# let us clean only our files.
myclean:
	rm -f *.vo *.glob *.v.d *.beautified *.old *.g *.vi

# let us clean only our files.
testclean:
	rm -rf _build
	cd sparktests; clean.sh

# build tags for our files + spark + compcert
tags:
	$COQTAGS $COMPCERT/*/*.v $SPARK/*.v *.v

" >> Makefile
