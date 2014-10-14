#!/bin/bash

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

# Getting the directory containing the current script and also the
# config file, which has default values for arguments
resourcedir=${0%/*}

# loding defaults
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


# Generate the _CoqProject file
cp $resourcedir/Config/_CoqProject.in ./_CoqProject
sed --posix -e "s/@COMPCERT/$COMPCERT/" ./_CoqProject | sponge ./_CoqProject
sed --posix -e "s/@SPARK/$SPARK/" ./_CoqProject | sponge ./_CoqProject

# I would like to be able to compile compcert from here but
# coq_makefile does not manage -R correctly.
find $COMPCERT/ -name "*svn*" -prune -o \( -name "*\.v" -print \) >>  ./_CoqProject
find $SPARK/ -name "*svn*" -prune -o -name "language_template\.v" -prune -o \( -name "*\.v" -print \) >>  ./_CoqProject

# Generate the Makefile from _CoqProject + add a coqtags target
coq_makefile -f _CoqProject > Makefile

# clean would clean Compcert, let us rename the target
sed --posix -e "s/clean:/superclean:/" ./Makefile | sponge ./Makefile



echo "
# ADDED BY build_make.sh:

# let us clean only our files.
clean:
	rm -f *.vo *.glob *.v.d *.beautified *.old *.g *.vi

# build tags for our files + spark + compcert
tags:
	$COQTAGS $COMPCERT/*/*.v $SPARK/*.v *.v

%.v:%.adb
	$SIREUM/sireum bakar program -p Coq \$*.adb \$*_template.v
	bash  $resourcedir/test_demo \$*_template.v \$*.v
" >> Makefile
