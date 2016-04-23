all:
	@echo no

doc:
	make -C boolchains/ doc
	make -C cweb/
	make -C cweb/ fullmanual
	make -C cweb/examples doc
	make -C dist/mf/ doc
	make -C dist/mfware/ doc
	make -C dist/tex/ doc
	make -C dist/texware/ doc
	make -C dist/web/ doc
	make -C mmix/ doc
	make -C sources/ doc

clean:
	git clean -dfx
	git reset --hard
