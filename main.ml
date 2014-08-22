#load "ass4_lexer.cmo";;
#load "ass4_parser.cmo";;

open Ass4_lexer ;;
open Ass4_parser ;;

let main () =
  try
    let lexbuf = Lexing.from_channel (open_in "myinput.txt") in
    while true do
      Ass4_parser.input Ass4_lexer.token lexbuf ;
    done
  with End_of_file -> exit 0 ;;
      
let _ = Printexc.print main () ;;

main() ;;