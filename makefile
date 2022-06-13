.PHONY: all
all: dpt_lisp.exe

dpt_lisp.exe: dpt_lisp/target/debug/dpt_lisp
	cp $< $@

dpt_lisp/target/debug/dpt_lisp: dpt_lisp/Cargo.toml dpt_lisp/src/*
	cd dpt_lisp && cargo build

.PHONY: test
test: dpt_lisp.exe tests/*.lsp
	./dpt_lisp.exe tests/*.lsp



.PHONY: clean
clean:
	cd dtp_lisp     && cargo clean
	cd dtp_lisp_web && cargo clean
