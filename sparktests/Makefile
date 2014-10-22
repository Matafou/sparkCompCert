
include ../.config

FLAGS=-S
CPP=cpp -P
AS=$(CASM)
CFLAGS=-g
ASFLAGS=



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

.c.o:
	$(CC) $(CFLAGS) -c $<

.s.o:
	$(AS) $(ASFLAGS) -o $*.o $<

.S.o:
	$(AS) $(ASFLAGS) -o $*.o $<

%.v: %.adb
	rm -f $@.template
	rm -f $@
	$(SIREUM)/sireum bakar program -p Coq $< $@.template
	echo "Require Import checks_comparison." >> $@
	echo "" >> $@  # insert newline
	sed -e 's/_xx//g;s/_XX//g;s/(\*checks\*)//g' $@.template >> $@
	rm -f $@.template
	echo >> $@
	echo >> $@
	echo "(* EXTRACTION COMMAND *)"  >> $@
	echo "(* This must stick to compcert extraction syle, or input_value will segfault... *)"  >> $@
	echo "Require Import ExtrOcamlBasic."  >> $@
	echo "Require Import ExtrOcamlString."  >> $@
	echo "Extraction \"$(@:.v=.ml)\" Symbol_Table Coq_AST_Tree." >> $@

clean::
	rm -f *proc*.v

%.ml: %.v
	coqc -R ../../ia32 compcert.ia32 -R ../../lib compcert.lib -R ../../common compcert.common -R ../../backend compcert.backend -R ../../cfrontend compcert.cfrontend -R ../../driver compcert.driver -R ../../flocq compcert.flocq -R ../../exportclight compcert.exportclight -R ../../cparser compcert.cparser -I ../spark $<
	echo ";;" >> $@
	echo "print_string \"generating ocaml values...\n\";" >> $@
	echo "let oc = open_out \"$(@:.ml=.mlo)\" in" >> $@
	echo "let _ = output_value oc (symbol_Table, coq_AST_Tree) in" >> $@
	echo "close_out oc" >> $@

clean::
	rm -f *proc*.ml*

%.mlo: %.ml
	ocamlbuild -I .. $(@:.mlo=.native)
	$(@:.mlo=.native)
	rm -f $(@:.mlo=.native)

clean::
	rm -f *.mlo

%.cm: %.mlo
	../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump -c $< -o $(<:.mlo=.o)
	rm $(<:.mlo=.o)

clean::
	rm -f *.cm *.s

%.exe: %.cm
	../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump -c $< -o $(<:.cm=.o)
	../../ccomp -stdlib ../../runtime -lm -dasm -dcminor -g -sdump $(<:.cm=.o) $(<:.cm=main.c) -o $@


clean::
	rm -f *.exe


.SECONDARY: $(PROGS:%=%.s)

clean::
	rm -f *.s *.o *~
