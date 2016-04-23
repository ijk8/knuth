all:
	@echo no

doc:
	weave weave.web
	tex weave.tex
	dvipdfm weave.dvi
	weave tangle.web
	tex tangle.tex
	dvipdfm tangle.dvi
	tex webman.tex
	dvipdfm webman.dvi

clean:
