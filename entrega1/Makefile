# Unix makefile for tigermain example

# Para nuestras casas
HOME=/usr/bin
MOSMLHOME=${HOME}
MOSMLTOOLS=$(MOSMLHOME)/camlrunm /usr/local/share/mosml/tools
MOSMLLEX=$(MOSMLHOME)/mosmllex
MOSMLYACC=$(MOSMLHOME)/mosmlyac -v


# Para el DCC
# HOME=/usr/local/bin
# MOSMLHOME=${HOME}
# MOSMLTOOLS=$(MOSMLHOME)/camlrunm $(MOSMLHOME)/tools
# MOSMLLEX=$(MOSMLHOME)/mosmllex
# MOSMLYACC=$(MOSMLHOME)/mosmlyac -v

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

GRALOBJS= tigerabs.uo tigergrm.uo tigerlex.uo tigermain.uo \
	tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo \
	tigerseman.uo tigertemp.uo topsort.uo  \
	tigertips.uo

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
tigerseman.uo: tigerseman.ui tigersres.uo tigertab.ui topsort.ui \
    tigertemp.ui tigerabs.uo tigerpp.uo 
tigertemp.uo: tigertemp.ui 
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigerpp.uo: tigertab.ui tigertips.uo tigerabs.uo 
tigerseman.ui: tigerabs.uo 
eje2.uo: eje2.ui tigerabs.uo 
tigertab.uo: tigertab.ui 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo 
tigerescap.uo: tigerescap.ui tigertab.ui tigerabs.uo 
tigerlex.uo: tigergrm.ui tigernlin.uo 
tigerescap.ui: tigerabs.uo 
eje2.ui: tigerabs.uo 
tigergrm.ui: tigerabs.uo 
topsort.uo: topsort.ui tigerabs.uo 
tigermain.uo: tigerseman.ui tigerescap.ui tigergrm.ui tigerlex.uo \
    tigerpp.uo 
