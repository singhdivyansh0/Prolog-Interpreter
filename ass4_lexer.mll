{
  open Printf
  open Ass4_parser
  
 let replace s = let l = String.length s in
             let p = ref 0 in
             while !p < l do
             if s.[!p] = '~' then 
             s.[!p] <- '-';
             p := !p + 1;
             done;;
}

let caps = ['A'-'Z']
let small = ['a'-'z']
let chars = ['A'-'Z' 'a'-'z' '0'-'9' ''' '_']


rule token = parse
  | '('   { LPARAN }
  | ')'   { RPARAN }
  | ","   { COMMA }
  | ":-"  { IF }
  | "."   { DOT }
  | '?'   { QUERY }
  | caps chars* as variables
    {
      VAR(variables)
    }
  | small chars* as text
    {
      ID(text)
    }
  | '\n' { NEWLINE }
  | _   { token lexbuf }
  | eof   { raise End_of_file }

