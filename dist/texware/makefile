all:
	@echo no

doc:
	weave dvitype.web
	tex dvitype.tex
	dvipdfm dvitype.dvi
	weave pltotf.web
	tex pltotf.tex
	dvipdfm pltotf.dvi
	weave pooltype.web
	tex pooltype.tex
	dvipdfm pooltype.dvi
	weave tftopl.web
	tex tftopl.tex
	dvipdfm tftopl.dvi

clean:
