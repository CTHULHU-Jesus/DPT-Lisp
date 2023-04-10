.PHONY: all
all: dpt_lisp.exe paper/paper.pdf web

dpt_lisp.exe: dpt_lisp/target/debug/dpt_lisp
	cp $< $@

dpt_lisp/target/debug/dpt_lisp: dpt_lisp/Cargo.toml dpt_lisp/src/*
	cd dpt_lisp && cargo build --features "build-binary"

.PHONY: web
web: 
	make -C dpt_lisp_web

.PHONY: paper/paper.pdf
paper/paper.pdf:
	make -C paper

.PHONY: test
test: dpt_lisp.exe tests/*.lsp
	./dpt_lisp.exe tests/*.lsp



.PHONY: clean
clean:
	rm -rf *~
	rm -rf */*~
	rm -rf */*/*~
	cd dtp_lisp     && cargo clean
	cd dtp_lisp_web && cargo clean
	make -C paper clean
	make -C dpt_lisp_web clean
