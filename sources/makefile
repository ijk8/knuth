#
#   Makefile for the Stanford GraphBase
#

#   Be sure that CWEB version 3.0 or greater is installed before proceeding!

#   Skip down to "SHORTCUT" if you're going to work only from the
#   current directory. (Recommended for serious users.)

#   Change SGBDIR to the directory where all GraphBase files will go:
#SGBDIR = /usr/local/sgb

#   Change DATADIR to the directory where GraphBase data files will go:
#DATADIR = $(SGBDIR)/data

#   Change INCLUDEDIR to the directory where GraphBase header files will go:
#INCLUDEDIR = $(SGBDIR)/include

#   Change LIBDIR to the directory where GraphBase library routines will go:
#LIBDIR = /usr/local/lib

#   Change BINDIR to the directory where installdemos will put demo programs:
#BINDIR = /usr/local/bin

#   Change CWEBINPUTS to the directory where CWEB include files will go:
#CWEBINPUTS = /usr/local/lib/cweb

#   SHORTCUT: Uncomment these lines, for single-directory installation:
DATADIR = .
INCLUDEDIR = .
LIBDIR = .
BINDIR = .
CWEBINPUTS = .

#   Uncomment the next line if your C uses <string.h> but not <strings.h>:
#SYS = -DSYSV

#   If you prefer optimization to debugging, change -g to something like -O:
CFLAGS = -g -I$(INCLUDEDIR) $(SYS)

########## You shouldn't have to change anything after this point ##########

LDFLAGS = -L$(LIBDIR)
LDLIBS = -lgb
LOADLIBES = $(LDLIBS)

.SUFFIXES: .dvi .pdf .tex .w

.tex.dvi:
	tex "\let\pdf+ \input $*.tex"

.dvi.pdf:
	dvipdfm $*.dvi

.w.c:
	if test -r $*.ch; then ctangle $*.w $*.ch; else ctangle $*.w; fi

.w.tex:
	if test -r $*.ch; then cweave $*.w $*.ch; else cweave $*.w; fi

.w.o:
	make $*.c
	make $*.o

.w:
	make $*.c
	make $*

.w.dvi:
	make $*.tex
	make $*.dvi

DATAFILES = anna.dat david.dat econ.dat games.dat homer.dat huck.dat \
        jean.dat lisa.dat miles.dat roget.dat words.dat
KERNELFILES = gb_flip.w gb_graph.w gb_io.w gb_sort.w
GENERATORFILES = gb_basic.w gb_books.w gb_econ.w gb_games.w gb_gates.w \
        gb_lisa.w gb_miles.w gb_plane.w gb_raman.w gb_rand.w gb_roget.w \
        gb_words.w
DEMOFILES = assign_lisa.w book_components.w econ_order.w football.w \
        girth.w ladders.w miles_span.w multiply.w queen.w roget_components.w \
        take_risc.w word_components.w
MISCWEBS = boilerplate.w gb_dijk.w gb_save.w gb_types.w test_sample.w
CHANGEFILES = queen_wrap.ch word_giant.ch
MISCFILES = Makefile README abstract.plaintex cities.texmap blank.w \
        sample.correct test.correct test.dat +The+Stanford+GraphBase+
SGBW = $(KERNELFILES) $(GENERATORFILES) $(DEMOFILES) gb_dijk.w gb_save.w \
        test_sample.w
DEKW = 15puzzle-korf0.w 15puzzle-korf1.w achain0.w achain1.w achain2.w \
        achain3.w achain4.w achain-all.w achain-decode.w advent.w \
        antislide3.w antislide.w back-20q.w back-commafree4.w \
        back-dissect.w back-mxn-words-mxn.w back-mxn-words-new.w back-pdi.w \
        back-skeleton-shortest.w bdd12.w bdd14.w bdd15.w bddl-rgrowth.w \
        bddread.w celtic-paths.w co-debruijn.w commafree-eastman-new.w \
        commafree-eastman.w dance.w decagon.w dimacs-to-sat.w domination.w \
        dot-diff.w dragon-calc.w embed.w erection.w euler-trail.w ezgraph.w \
        fchains4x.w flower-snark-line.w fog2mf.w francon.w garsia-wachs.w \
        gates-stuck.w                  gdance.w graph-cyc.w graph-sig-v0.w \
        grayspan.w grayspspan.w halftone.w hamdance.w ham.w horn-count.w \
        hulls.w hulltr.w hullt.w hull.w hwb-fast.w hyperbolic.w \
        koda-ruskey.w lagfib.w langford.w linked-trees.w li-ruskey.w lp.w \
        macmahon-triangles-sym-tile.w makeboard.w make_prod.w maxcliques.w \
                         obdd.w            polyenum.w polyiamonds.w \
        polynum.w polyominoes.w polyslave.w polysticks.w posets0.w posets.w \
        prime-sieve-sparse.w prime-sieve.w queen-graph.w queens.w \
        rand-d4g6.w random-ternary.w ran-prim.w reflect.w rost.w sand.w \
        sat0.w sat0w.w sat10.w sat11.w sat12-erp.w sat12.w sat13.w sat8.w \
        sat9.w sat-arithprog.w sat-chains.w sat-closest-string-dat.w \
                             sat-color-exclusion.w sat-color-kernel.w \
        sat-color-log2.w sat-color-log3.w sat-color-log.w sat-color-order.w \
        sat-color.w sat-commafree.w sat-connection.w sat-dadda.w \
        sat-dance.w sat-erdos-disc.w sat-eulerian-balance.w \
        sat-gates-stuck.w sat-graph-quench.w sat-life-filter.w sat-life.w \
        sat-mintime-sort.w sat-mutex.w sat-newlangford.w sat-oss.w \
        sat-poset-nomax.w sat-queens-color-order-cliques2.w \
        sat-queens-color-order-cliques.w sat-rand-rep.w sat-synth-data.w \
        sat-synth.w sat-tatami.w sat-threshold-bb-equal.w \
        sat-threshold-bb.w sat-threshold-sinz.w sat-to-dimacs.w \
        sat-tomography-filter.w sat-tomography-prep.w sat-tomography.w \
        sat-tseytin.w sat-waerden.w sat-zarank.w              \
        setset-random.w setset.w sham.w simpath-directed-cycles.w \
        simpath-reduce.w simpath.w                     sliding.w spgraph.w \
        spiders.w spspan.w squaregraph-rand.w squaregraph.w straighten.w \
        strongchain.w sudoku.w tcalc.w tictactoe0.w tictactoe1.w \
        tictactoe2.w tictactoe3.w tictactoe4.w tictactoe5.w tictactoe6.w \
        tictactoe7.w togpap.w topswops-fwd.w topswops.w             ulam.w \
        unavoidable2.w unavoidable.w vacillate.w viennot.w xgdance.w \
        yplay.w zeilberger.w
FIXW = gates-to-wires.w mcgregor-graph.w oss-data.w sat-closest-string.w \
        setset-all.w skew-ternary-calc.w treeprobs.w
ALL = $(DATAFILES) $(KERNELFILES) $(GENERATORFILES) $(DEMOFILES) \
        $(MISCWEBS) $(CHANGEFILES) $(MISCFILES)

OBJS = $(KERNELFILES:.w=.o) $(GENERATORFILES:.w=.o) gb_dijk.o gb_save.o
HEADERS = $(OBJS:.o=.h)
DEMOS = $(DEMOFILES:.w=)
PDFS = $(SGBW:.w=.pdf) $(DEKW:.w=.pdf)

help:
	@ echo "First 'make tests';"
	@ echo "then (optionally) 'make installdemos';"
	@ echo "then (optionally) 'make clean'."

lib: libgb.a

libgb.a: $(OBJS)
	rm -f certified
	ar rcv libgb.a $(OBJS)
	- ranlib libgb.a

gb_io.o: gb_io.c
	$(CC) $(CFLAGS) -DDATA_DIRECTORY=\"$(DATADIR)/\" -c gb_io.c

test_io: gb_io.o
	$(CC) $(CFLAGS) test_io.c gb_io.o -o test_io

test_graph: gb_graph.o
	$(CC) $(CFLAGS) test_graph.c gb_graph.o -o test_graph

test_flip: gb_flip.o
	$(CC) $(CFLAGS) test_flip.c gb_flip.o -o test_flip

tests: test_io test_graph test_flip
	./test_io
	./test_graph
	./test_flip
	make gb_sort.o
	make lib
	make test_sample
	- ./test_sample > sample.out
	diff test.gb test.correct
	diff sample.out sample.correct
	rm test.gb sample.out test_io test_graph test_flip test_sample
	echo "Congratulations --- the tests have all been passed."
	touch certified

installdemos: lib $(DEMOS)

uninstalldemos:
	- cd $(BINDIR); rm -f $(DEMOS)

figs:
	mpost hyperbolic.mp
	mpost kepler.mp
#	mpost li-ruskey.mp
	mpost polyomino.mp
	mpost sgbfig.mp
	mpost skew-ternary-calc.mp
	mpost spspan.mp

doc: figs $(PDFS)
	tex abstract.plaintex
	dvipdfm abstract.dvi

clean:
	@git reset --hard
	@git clean -dfx

veryclean: clean
	rm -f $(DEMOS)
