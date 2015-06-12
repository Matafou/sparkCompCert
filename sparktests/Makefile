
# ../.config should conatin at least a line:
# SIREUM=/home/foo/bat/Sireum
include ../.config

FLAGS=-S
CPP=cpp -P
AS=$(CASM)
CFLAGS=-g
ASFLAGS=
COQTAGS= -R ../../ia32 compcert.ia32 -R ../../lib compcert.lib -R ../../common compcert.common -R ../../backend compcert.backend -R ../../cfrontend compcert.cfrontend -R ../../driver compcert.driver -R ../../flocq compcert.flocq -R ../../exportclight compcert.exportclight -R ../../cparser compcert.cparser -R ../../spark spark  -R ../../sparkfrontend sparkfrontend
CC=../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump


.SUFFIXES:

.SUFFIXES: .cmp .cm .s .o .c .S .mlo

.cmp.s:
	$(CPP) $*.cmp > $*.cm
	$(CCOMP) $(FLAGS) $*.cm

.adb.s:
	../sparkcomp $*.adb
	$(CCOMP) $(FLAGS) $*.cm

.cm.s:
	$(CCOMP) $(FLAGS) $*.cm

.c.cm:
	../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump -c $< -o $(@:.cm=.o)
	rm -f $(<:.c=.o)
.cm.o:
	../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump -c $< -o $@



#.s.o:
#	$(AS) $(ASFLAGS) -o $*.o $<

#.S.o:
#	$(AS) $(ASFLAGS) -o $*.o $<

# TODO: have an error when Sireum prints an error message.
# or have sireum return an error code instead.
%.v: %.adb
	rm -f $@.template
	rm -f $@
	$(SIREUM)/sireum bakar program -p Coq $< $@
	echo >> $@
	echo >> $@
	echo "(* EXTRACTION COMMAND *)"  >> $@
	echo "(* This must stick to compcert extraction syle, or input_value will segfault... *)"  >> $@
	echo "Require Import ExtrOcamlBasic."  >> $@
	echo "Require Import ExtrOcamlString."  >> $@
	echo "Extraction \"$(@:.v=.ml)\" Symbol_Table Coq_AST_Tree." >> $@

	sed -i -e 's/Require Import checks_comparison\.//' $@

clean::
	rm -f *proc*.v

%.ml: %.v
	coqc $(COQTAGS) $<
	echo ";;" >> $@
	echo "print_string \"generating ocaml values...\n\";" >> $@
	echo "let oc = open_out \"$(@:.ml=.mlo)\" in" >> $@
	echo "let _ = output_value oc (symbol_Table, coq_AST_Tree) in" >> $@
	echo "close_out oc" >> $@

clean::
	rm -f *proc*.ml* *.vo *.glob

%.mlo: %.ml
	ocamlbuild -no-hygiene -I .. $(@:.mlo=.native)
	$(@:.mlo=.native)
	rm -f $(@:.mlo=.native)

clean::
	rm -f *.mlo

%.cm: %.mlo
	../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump -c $< -o $(<:.mlo=.o)

clean::
	rm -f *.cm *.s

clean::
	rm -f *.exe


.SECONDARY: $(PROGS:%=%.s)

clean::
	rm -f *.s *.o *~ *.sdump

%.exe: %main.o  %.o
	../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump $(@:.exe=.o) $(@:.exe=main.o) -o $@

proc0.exe:: proc0main.c proc0.o
proc1.exe:: proc1main.o proc1.o
proc2.exe:: proc2main.o proc2.o
proc3.exe:: proc3main.o proc3.o
proc4.exe:: proc4main.o proc4.o
proc5.exe:: proc5main.o proc5.o
proc6.exe:: proc6main.o proc6.o
#g.exe:: gmain.o g.o

clean::
	rm -f g.exe g.v g.ml g.mli 
	rm -f gnatinspect.db*
	rm -f *.ali
