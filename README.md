# sys4dc

This is an experimental decompiler for AliceSoft's System4 game engine.
Currently it supports games released between 2003 (Daibanchou) and 2015
(Rance 03).

## Installation

To build and install `sys4dc` from source code, you need to have OCaml and opam
installed. Then, run the following commands:

```sh
$ git clone --recursive https://github.com/kichikuou/sys4dc.git
$ cd sys4dc
$ opam install . --deps-only
$ dune build
$ dune install
```
