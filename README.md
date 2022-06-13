# DPT-Lisp

[![Build](https://github.com/CTHULHU-Jesus/DPT-Lisp/actions/workflows/build.yml/badge.svg)](https://github.com/CTHULHU-Jesus/DPT-Lisp/actions/workflows/build.yml)
[![Build-Web](https://github.com/CTHULHU-Jesus/DPT-Lisp/actions/workflows/build-web.yml/badge.svg)](https://github.com/CTHULHU-Jesus/DPT-Lisp/actions/workflows/build-web.yml)
[![Test](https://github.com/CTHULHU-Jesus/DPT-Lisp/actions/workflows/test.yml/badge.svg)](https://github.com/CTHULHU-Jesus/DPT-Lisp/actions/workflows/test.yml)

a dependently typed lisp

# Purpose


The purpose of this project is to create a dependently typed lisp-like language. This is ment to be an inplimentation of the work for my masters thesis. There will also be a web version where people can interact with the interpreter.

# Bugs

- The REPL history is not stored in the home directory.

# Missing Features

- types
- ports 
- standard library
- website

# Completed features Features

- Let expressions
- printing
- initial parsing and evaluation



# Recorces

- Parser
  - [nom](https://docs.rs/nom/latest/nom/) - A parsing combinator library.
  - [nom-locate](https://docs.rs/nom_locate/latest/nom_locate/) - Allows for position tracking while parsing.
- [Rust your own lisp](https://dev.to/deciduously/rust-your-own-lisp-50an)
  - [rustyline](https://github.com/kkawakam/rustyline) - a rust implimentation of readline.
  - Ast help

- [Build your own Lisp](https://buildyourownlisp.com/contents)
- [Scope](https://craftinginterpreters.com/statements-and-state.html#scope)
