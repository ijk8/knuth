all:
	@echo no

doc:
	weave mf.web
	tex mf.tex
	dvipdfm mf.dvi
	tex trapman.tex
	dvipdfm trapman.dvi

clean:
