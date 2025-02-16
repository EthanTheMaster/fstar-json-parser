#!/bin/bash

rm -rf out/
fstar.exe --codegen OCaml --extract Json --odir out Json.Main.fst
cd out/
# Make sure to set OCAMLPATH=$FSTAR_HOME/lib
ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib -r Json_Main.native
cp Json_Main.native ../