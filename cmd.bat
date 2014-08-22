ocamlc -c types.ml
ocamlyacc ass4_parser.mly
ocamlc -c ass4_parser.mli
ocamllex ass4_lexer.mll
ocamlc -c ass4_lexer.ml
ocamlc -c ass4_parser.ml
ocamlc -c main.ml
ocaml < main.ml