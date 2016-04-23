all:
	@echo no

doc:
	weave tex.web
	tex tex.tex
	dvipdfm tex.dvi
	weave glue.web
	tex glue.tex
	dvipdfm glue.dvi
	tex tripman.tex
	dvipdfm tripman.dvi

clean:
