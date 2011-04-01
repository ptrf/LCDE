
##############################################################################
# Variables
##############################################################################
TARGET=deckard

SRC=context.mli context.ml \
	deckard_types.mli deckard_types.ml \
	charv.mli charv.ml \
	deckard_configuration.ml \
	infixes.ml \
	reader.ml \
	process.ml \
	merge.ml \
	prune.ml \
	lsh.ml \
	main.ml

COCCI=../vanillacocci
OCAMLGSLSRC=../ocamlgsl-0.6.0
OCAMLGSL=../gsl

SYSLIBS=str.cma unix.cma bigarray.cma nums.cma

LIBS=$(COCCI)/commons/commons.cma $(COCCI)/globals/globals.cma \
	 $(COCCI)/parsing_cocci/cocci_parser.cma $(COCCI)/parsing_c/parsing_c.cma \
	 $(OCAMLGSL)/gsl.cma

MAKESUBDIRS=$(COCCI)/commons $(COCCI)/globals $(COCCI)/menhirlib $(COCCI)/parsing_cocci $(COCCI)/parsing_c \
			$(COCCI)/parsing_cocci $(OCAMLGSLSRC)

INCLUDEDIRS=$(COCCI)/commons $(COCCI)/commons/ocamlextra $(COCCI)/globals $(COCCI)/commons/ocollection \
			$(COCCI)/parsing_c $(COCCI)/parsing_cocci $(OCAMLGSL)

##############################################################################
# Generic variables
##############################################################################

INCLUDES=$(INCLUDEDIRS:%=-I %)

OBJS=    $(SRC:.ml=.cmo)
OPTOBJS= $(SRC:.ml=.cmx)

EXEC=$(TARGET)

##############################################################################
# Generic ocaml variables
##############################################################################

OCAMLCFLAGS=-dtypes -custom -w A

# for profiling add  -p -inline 0
# but 'make forprofiling' below does that for you.
# This flag is also used in subdirectories so don't change its name here.
OPTFLAGS=-dtypes

# the OPTBIN variable is here to allow to use ocamlc.opt instead of
# ocaml, when it is available, which speeds up compilation. So
# if you want the fast version of the ocaml chain tools, set this var
# or setenv it to ".opt" in your startup script.
OPTBIN=

OCAMLC=ocamlc$(OPTBIN) $(OCAMLCFLAGS)  $(INCLUDES)
OCAMLOPT=ocamlopt$(OPTBIN) $(OPTFLAGS) $(INCLUDES)
OCAMLLEX=ocamllex #-ml # -ml for debugging lexer, but slightly slower
OCAMLYACC=ocamlyacc -v
OCAMLDEP=ocamldep #$(INCLUDES)
OCAMLMKTOP=ocamlmktop -g -custom $(INCLUDES)


##############################################################################
# Top rules
##############################################################################

all: rec $(EXEC)
opt: rec.opt $(EXEC).opt

rec:
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i all; done ; $(MAKE) -C $(OCAMLGSLSRC) install;
rec.opt:
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i all.opt; done 

#genericp: genericlexer.mll genericparser.mly
#	echo "Generating lexer..."
#	ocamllex genericlexer.mll
#	echo "Generating parser..."
#	menhir genericparser.mly

$(EXEC): $(LIBS) $(OBJS)
	$(OCAMLC) -o $@ $(SYSLIBS) $^

$(EXEC).top: $(LIBS) $(OBJS)
	$(OCAMLMKTOP) -o $@ $(SYSLIBS) $^

clean::
	rm -f $(TARGET) $(TARGET).top

clean::
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i clean; done

localclean:
	rm -f $(TARGET) $(TARGET).top *~ .*~ *.exe *.cm[iox] *.o *.annot

##############################################################################
# Generic ocaml rules
##############################################################################

.SUFFIXES: .ml .mli .cmo .cmi .cmx .cmxa

.ml.cmo:
	$(OCAMLC)  -c $<
.mli.cmi:
	$(OCAMLC)  -c $<
.ml.cmx:
	$(OCAMLOPT)  -c $<

.ml.mldepend: 
	$(OCAMLC) -i $< 


clean::
	rm -f *.cm[iox] *.o *.annot

clean::
	rm -f *~ .*~ *.exe #*#

#depend:: genericp
depend::
	$(OCAMLDEP) *.mli *.ml > .depend
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i depend; done

-include .depend
