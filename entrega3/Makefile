# Unix makefile for tigermain example

# Para nuestras casas
#HOME=/usr/bin
#MOSMLHOME=${HOME}
#MOSMLTOOLS=$(MOSMLHOME)/camlrunm /usr/local/share/mosml/tools
#MOSMLLEX=$(MOSMLHOME)/mosmllex
#MOSMLYACC=$(MOSMLHOME)/mosmlyac -v

# Para el DCC y lab. de 2º piso
HOME=/usr/local/bin
MOSMLHOME=${HOME}
MOSMLTOOLS=$(MOSMLHOME)/camlrunm $(MOSMLHOME)/tools
MOSMLLEX=$(MOSMLHOME)/mosmllex
MOSMLYACC=$(MOSMLHOME)/mosmlyac -v

GCC=gcc
CFLAGS= -g
MOSMLC=${MOSMLHOME}/mosmlc -c -liberal
MOSMLL=${MOSMLHOME}/mosmlc

# Para el laboratorio
# HOME=/home/alumno
# MOSMLHOME=${HOME}/mosml
# MOSMLTOOLS=${MOSMLHOME}/bin/camlrunm ${MOSMLHOME}/tools
# MOSMLLEX=${MOSMLHOME}/bin/mosmllex
# MOSMLYACC=${MOSMLHOME}/bin/mosmlyac -v

# GCC=gcc
# CFLAGS= -g
# MOSMLC=${MOSMLHOME}/bin/mosmlc -c -liberal
# MOSMLL=${MOSMLHOME}/bin/mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

# DOS
#REMOVE=del
#MOVE=move
#EXEFILE=.exe

.SUFFIXES :
.SUFFIXES : .sig .sml .ui .uo

# GRALOBJS= tigerabs.uo tigergrm.uo tigerlex.uo tigermain.uo \
# 	tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo \
# 	tigerseman.uo tigertemp.uo topsort.uo  \
# 	tigertips.uo

GRALOBJS= tigerabs.uo tigergrm.uo tigerlex.uo tigermain.uo \
	  tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo tigerseman.uo tigertemp.uo topsort.uo tigertree.uo \
	  tigerframe.uo tigertrans.uo tigerit.uo tigerpila.uo tigercanon.uo \
	  tigerassem.uo tigercodegen.uo tigergraph.uo tigerflow.uo tigermg.uo tigerliveness.uo tigercolor.uo \
	  tigersimpleregalloc.uo tigerconstants.uo tigerregalloc.uo


all: tiger

tiger: $(GRALOBJS) $(OBJSGEN)
	$(MOSMLL) -o tiger $(EXEFILE) tigermain.uo

tigergrm.sml tigergrm.sig: tigergrm.y 
	$(MOSMLYACC) tigergrm.y

tigerlex.sml: tigerlex.lex
	$(MOSMLLEX) tigerlex.lex

clean:
	$(REMOVE) Makefile.bak
	$(REMOVE) tigergrm.output
	$(REMOVE) tigergrm.sig
	$(REMOVE) tigergrm.sml
	$(REMOVE) tigerlex.sml
	$(REMOVE) tigermain
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: tigerabs.sml tigergrm.sml tigerlex.sml tigermain.sml \
	tigernlin.sml tigerpp.sml \
	topsort.sml
	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
tigerseman.uo: tigerseman.ui tigersres.uo tigertab.ui tigerpila.ui \
    topsort.ui tigerabs.uo tigertrans.ui tigerit.uo
tigercanon.uo: tigercanon.ui tigertree.uo tigertab.ui tigertemp.ui 
tigerinterp.uo: tigertree.uo tigertab.ui tigerframe.ui tigerit.uo \
    tigertemp.ui 
tigertemp.uo: tigertemp.ui 
tigertrans.uo: tigertrans.ui tigertree.uo tigerpila.ui tigerframe.ui \
    tigerit.uo tigertemp.ui tigerabs.uo tigerregalloc.ui tigercodegen.ui \
    tigercolor.ui
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigerpp.uo: tigertab.ui tigertips.uo tigerabs.uo 
tigerseman.ui: tigerabs.uo 
tigertab.uo: tigertab.ui 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo \
    tigertrans.ui 
tigertree.uo: tigertemp.ui 
tigerescap.uo: tigerescap.ui tigertab.ui tigerabs.uo 
tigerframe.ui: tigertree.uo tigertemp.ui tigerassem.uo
tigertrans.ui: tigertree.uo tigerframe.ui tigertemp.ui tigerabs.uo 
tigerit.uo: tigertree.uo tigertab.ui 
tigerlex.uo: tigergrm.ui tigernlin.uo 
tigerescap.ui: tigerabs.uo 
tigerpila.uo: tigerpila.ui 
tigergrm.ui: tigerabs.uo 
topsort.uo: topsort.ui tigerabs.uo 
tigercanon.ui: tigertree.uo 
tigermain.uo: tigerseman.ui tigerescap.ui tigergrm.ui tigerlex.uo \
    tigerpp.uo tigertrans.uo tigercodegen.ui tigercanon.ui tigerinterp.uo \
    tigersimpleregalloc.ui
tigerframe.uo: tigerframe.ui tigertree.uo tigertemp.ui
tigercodegen.uo: tigercodegen.ui tigertemp.ui tigerconstants.ui
tigercodegen.ui: tigerframe.ui tigerassem.uo tigertree.uo
tigerassem.uo: tigertemp.ui
tigergraph.uo: tigertemp.ui tigergraph.ui
tigerflow.uo: tigertemp.ui tigergraph.ui
tigermg.ui: tigerassem.uo tigerflow.ui
tigermg.uo: tigermg.ui tigergraph.ui tigergraph.uo tigerflow.uo tigerassem.uo
tigerliveness.ui: tigergraph.ui tigertemp.ui tigerflow.uo
tigerliveness.uo: tigerliveness.ui tigergraph.uo
tigercolor.ui: tigerframe.ui tigertemp.ui tigerliveness.ui tigergraph.ui
tigercolor.uo: tigercolor.ui tigerassem.ui
tigersimpleregalloc.ui: tigerframe.ui tigerassem.ui
tigersimpleregalloc.uo: tigersimpleregalloc.ui tigerframe.ui tigerassem.ui tigerflow.ui
tigerconstants.uo: tigerconstants.ui
tigerregalloc.ui: tigerassem.ui tigercolor.ui tigerframe.ui
tigerregalloc.uo: tigerregalloc.ui tigercolor.ui tigerframe.ui