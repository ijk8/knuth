all:
	@echo no

doc:
	make -C boolchains/ doc
	make -C cweb/
	make -C cweb/ fullmanual
	make -C cweb/examples doc
	make -C mmix/ doc
	make -C sources/ doc

clean:
	git clean -dfx
	git reset --hard
