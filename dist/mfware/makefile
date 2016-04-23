all:
	@echo no

doc:
	weave gftodvi.web
	tex gftodvi.tex
	dvipdfm gftodvi.dvi
	weave gftopk.web
	tex gftopk.tex
	dvipdfm gftopk.dvi
	weave gftype.web
	tex gftype.tex
	dvipdfm gftype.dvi
	weave mft.web
	tex mft.tex
	dvipdfm mft.dvi

clean:
