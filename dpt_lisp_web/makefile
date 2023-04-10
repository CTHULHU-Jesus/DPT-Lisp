.PHONY: all
all: index.css target/wasm32-unknown-unknown/debug/dpt_lisp_web.wasm 

index.css: index.scss
	sass $< $@

target/wasm32-unknown-unknown/debug/dpt_lisp_web.wasm: Cargo.toml src/* index.html index.css
	trunk build

.PHONY: run
run: all
	trunk serve 

.PHONY: clean
clean: clean
	trunk clean
	rm index.css
	rm -rf src/*~
	rm  *~



