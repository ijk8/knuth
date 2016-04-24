all:
	@echo no

doc:
	weave vftovp.web
	tex vftovp.tex
	dvipdfm vftovp.dvi
	weave vptovf.web
	tex vptovf.tex
	dvipdfm vptovf.dvi

clean:
