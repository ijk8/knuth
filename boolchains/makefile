CC = cc
CFLAGS = -g
WFILES = 5chains0.w 5chainsi.w 5chainst.w 5chainsx.w 5chainsy.w \
        boolcode.w fchains5.w schains.w

#======================================================================

.SUFFIXES: .tex .dvi .pdf .w

.w.tex:
	cweave $*

.tex.dvi:	
	tex "\let\pdf+ \input $*.tex"

.dvi.pdf:
	dvipdfm $*.dvi

.w.dvi:
	make $*.tex
	make $*.dvi

.w.c:
	ctangle $*

.w.o:
	make $*.c
	make $*.o

.c.o:
	$(CC) $(CFLAGS) -c $*.c

.w:
	make $*.c
	$(CC) $(CFLAGS) $*.c -o $*

#======================================================================

all: $(WFILES:.w=)

doc: $(WFILES:.w=.pdf)

clean:
