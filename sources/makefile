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

.SUFFIXES: .dvi .tex .w

.tex.dvi:
	tex $*.tex

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
ALL = $(DATAFILES) $(KERNELFILES) $(GENERATORFILES) $(DEMOFILES) \
        $(MISCWEBS) $(CHANGEFILES) $(MISCFILES)

OBJS = $(KERNELFILES:.w=.o) $(GENERATORFILES:.w=.o) gb_dijk.o gb_save.o
HEADERS = $(OBJS:.o=.h)
DEMOS = $(DEMOFILES:.w=)

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

doc:
	tex abstract.plaintex

clean:
	@git reset --hard
	@git clean -dfx

veryclean: clean
	rm -f $(DEMOS)
