type token =
  | NEWLINE
  | COMMA
  | IF
  | DOT
  | QUERY
  | ID of (string)
  | VAR of (string)
  | LPARAN
  | RPARAN

open Parsing;;
let _ = parse_error;;
# 2 "ass4_parser.mly"
open Printf ;;
open Types ;;
let stack = ref[] ;;


let print_subst l = 
let rec print_ans l =
match l with             [] -> ""
                        |(Var(a),Var(b))::xs -> 
                        if (a.[0] <> '_') then (String.concat "" [a;"->";b;",";(print_ans xs)]) 
                        else (print_ans xs)
                        |(Var(a),Id(b))::xs -> 
                        if (a.[0] <> '_') then (String.concat "" [a;"->";b;",";(print_ans xs)])
                        else (print_ans xs)
                        |(Var(a),AT(s,l))::xs -> 
                        if (a.[0] <> '_') then  (String.concat "" [a;"->";"Term";"(";s;",";"l)";",";(print_ans xs)])
                        else (print_ans xs)
                        |_ -> ""
                        in
                    printf "%s\n" (print_ans l);;

let to_atom_pred t = match t with
                                                AT(x,y) -> (x,y) 
                                               |_ -> (" ",[])
;;                                               

let rec mapping f l =  match l with
                        [] -> []
                      | x::xs -> (f x)::(mapping f xs)
;;  

let extract_string p = 
  match p with AT((s,l)) -> s
        | Var x -> x 
        | Id b ->  b 
        ;;
let extract_list p = 
  match p with AT((s,l)) -> l ;;

let well_form atom ht = 
        let a = extract_string(atom) in
        let b = List.length(extract_list(atom)) in 
        try 
        (
           let c = Hashtbl.find ht a in
           if(b=c) then (true) else (false) ; 
          )
        with Not_found ->  Hashtbl.add ht a b  ; true;;

let rec well_list atom_list ht =
match List.hd(atom_list) with (a,l) -> 
 if(well_form (AT(a,l)) (ht)=true) then 
 (
  if(List.length(List.tl(atom_list))>0 ) then( 
  well_list (List.tl(atom_list)) (ht) ; )
  else (true) ;
  )
 else(false) ;;

let rec well list ht= 
      if(List.length(list)=0) then (true)
      else(
        match List.hd(list) with FACT(a,l) ->  if(well_form (AT(a,l)) (ht) =true) then ( well (List.tl(list)) (ht)) else (false); 
                                  | RULE((a,l),l1) -> if((well_form (AT(a,l)) (ht)) && well_list (l1) (ht) = true) then ( well (List.tl(list)) (ht) ) else (false) ;
                                    ) ;
      ;;


let rec substterm lst var =
  
  match var with
  Var x ->  
  (try (
     List.assoc (var) lst ;
    )
  with Not_found -> var )
  | AT(s,[]) -> (var)
  | AT(s,l) -> ( let i = ref 0 and  sub_list = ref [] in  
    ( while(!i < List.length(l)) do 
      sub_list := !sub_list@[substterm (lst) (List.nth l !i)] ;
      i := !i +1 ;
      done; 
      AT(s,!sub_list) ;
    )
)
  | _ -> var
  ;;

let rec substatom sb at =
              match at with
              (x,xs) -> let t = AT(x,xs) in
              to_atom_pred (substterm sb t)
                      ;;
let composition lst1 lst2 = 
let compo = ref [] and i =ref(0) in 
while(!i<List.length(!lst1)) do 
let j = ref(0) in 
let check = ref(false) in 
while(!j<List.length(!lst2)) do
if (snd(List.nth !lst1 !i)=fst(List.nth !lst2 !j)) then (
  compo := !compo@[fst(List.nth !lst1 !i),snd(List.nth !lst2 !j)] ;
  check := true ;
)
else();
j := !j + 1 ;
done;
if(!check =true) then ()
else(
compo := !compo@[fst(List.nth !lst1 !i),snd(List.nth !lst1 !i)] ;
);
i := !i+1 ;
done;
let i1 = ref(0) in 
while(!i1<List.length(!lst1)) do 
let j1 = ref(0) in 
while(!j1<List.length(!lst2)) do
if(fst(List.nth !lst1 !i1)=fst(List.nth !lst2 !j1)) then
(
lst2 := List.remove_assoc (fst(List.nth !lst2 !j1)) !lst2;
j1:=!j1-1 ;
)
else();
j1 := !j1 + 1 ;
done;
i1 := !i1+1 ;
done;

compo := !compo@(!lst2) ;

let i3 = ref(0)  and new_l = ref([]) in 
while (!i3<List.length(!compo)) do
  new_l := !new_l@[fst(List.nth !compo !i3),substterm (!compo) (snd(List.nth !compo !i3))] ;
  i3 := !i3+1 ; 
done ;
!new_l;;

let find_bool = ref(false) ;;
let rec find t x  = 
match t with Var y -> (if (t=x) then ( 
          find_bool := true ;
            !find_bool ;
          ) else(
            !find_bool ;
          );

)
      | AT(s,[]) -> (!find_bool;)
      |AT(s,l) -> ( let i= ref(0) in
      while (!i < List.length(l)) do
      find (List.nth l !i) (x) ;
      i := !i+1 ;
      done;
!find_bool;

 );;

let mgu_l = ref([]) ;;
exception NonUnify ;;

let rec mgu_1 t1 t2 mgu_l =   
  match t1 with Var(x) -> (match t2 with Var(y) -> 
                      (
                       if(extract_string(t1)=extract_string(t2)) then (!mgu_l)
                    else( mgu_l := (composition (mgu_l) (ref[(Var(x),Var(y))]) ) ; !mgu_l)
                  ; 
               )
                    | AT(s,[]) -> ( mgu_l := composition (mgu_l) (ref[(Var(x),AT(s,[]))]) ; !mgu_l )
                    |AT(a,l) -> (if((find (t2) (t1))=true) then (
                            find_bool := false ;
                            raise NonUnify ;
                    )
                  else(
                    mgu_l :=composition (mgu_l) (ref([(Var x,t2)]));
                      !mgu_l ;
                  );
                )
                    | _ -> ( ( mgu_l := (composition (mgu_l) (ref[(Var(x),t2)]) ) ; !mgu_l))

                    )

          |AT(s,[]) -> (match t2 with AT(b,[]) -> 
                    if(extract_string(t1)=extract_string(t2)) then (!mgu_l)
                    else(raise NonUnify );
                        | AT(e,l) -> (raise NonUnify )
                        | Var(x) ->  (mgu_l :=composition (mgu_l) (ref[(Var(x),AT(s,[]))]) ; !mgu_l)
                        | _ -> (raise NonUnify)
                        )
          | AT(a,l) -> (match t2 with AT(b,l1) ->

(
            if(List.length(l)=List.length(l1) && extract_string(t1)=extract_string(t2)) then (
              let i = ref(0) in 
              while (!i<List.length(l)) do
              if(List.length(!mgu_l)=0) then (
              

                mgu_1 (List.nth l !i) (List.nth l1 !i) mgu_l ;


                 !mgu_l ; )
            else(
              mgu_1 (substterm !mgu_l (List.nth l !i) ) (substterm !mgu_l (List.nth l1 !i)) (mgu_l) ;
              !mgu_l ;  
            );  
            i := !i+1 ;
              done;
                !mgu_l ;
            )
          else(raise NonUnify );
          )
          | Var(x) -> (if((find (t1) (t2))=true) then (
                            find_bool := false ;
                            raise NonUnify ;
                    )
                  else(
                    mgu_l :=composition (mgu_l) (ref([(Var(x),t1)]));
                    !mgu_l; 

                  );
                ) 
                  | _ -> (raise NonUnify)
                       )

            | _ -> ( match t2 with Var(x) -> (  mgu_l :=composition (mgu_l) (ref([(Var(x),t1)])); !mgu_l)
                                    |AT(s,l) -> (raise NonUnify)
                                    |_ -> (if (t1 <> t2) then raise NonUnify else !mgu_l )


              ) ;
            !mgu_l;;


let mgu t1 t2 = 
            match (t1,t2) with
            ((x,xs),(y,ys)) ->  mgu_1 (AT(x,xs)) (AT(y,ys)) (ref([])) ;;
            
let pointer = ref(0);;

let rec replacer t = 
                  match t with Var(v) -> Var(String.concat "" ["_";v;(string_of_int !pointer);])
                  | AT(s,l) -> AT(s,mapping replacer l)
                  | _ -> t     ;;                                                 

let rec repatom at= 
 match at with
(x,xs) -> to_atom_pred( replacer(AT(x,xs)))
;;                                

let rec renaming cl = match cl with
                                        FACT(at) -> pointer := !pointer + 1; FACT(repatom at);| RULE(hd,bd) -> pointer := !pointer + 1; RULE(repatom hd, mapping (repatom) bd); 
;;                              

let rec find_bindings query final = 
 match query with 
 [] -> printf("Bindings : "); print_subst(final); true;
| l::ls -> let hornclauses = !stack in
  if((List.length hornclauses) = 0) 
    then 
  (
false ;
)
else
 ( let ctr = ref(false) in                                      
for i=0 to ((List.length hornclauses)-1) do

let after_renaming = (renaming(List.nth hornclauses i)) in
match after_renaming with 
FACT(a,b) -> 
 (try   
let eval = mgu (a,b) l in
let g = (mapping (substatom eval) ls) in
let final1 = composition (ref(final)) (ref(eval)) in
ctr := (find_bindings g final1)
 || !ctr;
with NonUnify -> ();)
| RULE(a1,b1) -> 
(try  
let eval = (mgu a1 l) in 
let go = (mapping (substatom eval) (b1@ls) ) in 
let final1 = composition (ref(final)) (ref(eval)) in                                 
ctr := (find_bindings go final1) 
|| !ctr;
with NonUnify -> ();)
done;
!ctr
      );;


let answer query final = 
    (printf "%b\n" (find_bindings query final))
;;       

  
# 309 "ass4_parser.ml"
let yytransl_const = [|
  257 (* NEWLINE *);
  258 (* COMMA *);
  259 (* IF *);
  260 (* DOT *);
  261 (* QUERY *);
  264 (* LPARAN *);
  265 (* RPARAN *);
    0|]

let yytransl_block = [|
  262 (* ID *);
  263 (* VAR *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\002\000\003\000\
\004\000\005\000\007\000\008\000\008\000\006\000\010\000\010\000\
\009\000\009\000\011\000\011\000\000\000"

let yylen = "\002\000\
\000\000\002\000\001\000\002\000\002\000\002\000\002\000\002\000\
\004\000\002\000\001\000\001\000\003\000\004\000\001\000\004\000\
\001\000\003\000\001\000\001\000\002\000"

let yydefred = "\000\000\
\001\000\000\000\000\000\000\000\003\000\000\000\002\000\000\000\
\000\000\000\000\000\000\000\000\000\000\004\000\000\000\005\000\
\006\000\007\000\000\000\008\000\000\000\010\000\000\000\020\000\
\000\000\000\000\015\000\000\000\013\000\000\000\000\000\014\000\
\000\000\009\000\000\000\018\000\016\000"

let yydgoto = "\002\000\
\003\000\007\000\008\000\009\000\010\000\028\000\012\000\013\000\
\025\000\026\000\027\000"

let yysindex = "\004\000\
\000\000\000\000\002\255\000\255\000\000\006\255\000\000\019\255\
\020\255\021\255\007\255\022\255\018\255\000\000\010\255\000\000\
\000\000\000\000\023\255\000\000\023\255\000\000\016\255\000\000\
\017\255\025\255\000\000\026\255\000\000\027\255\010\255\000\000\
\010\255\000\000\024\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\001\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\254\254\000\000\
\000\000\028\255\000\000\014\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\029\000\000\000\247\255\
\238\255\000\000\000\000"

let yytablesize = 37
let yytable = "\019\000\
\014\000\004\000\005\000\011\000\001\000\012\000\019\000\006\000\
\019\000\029\000\020\000\030\000\035\000\015\000\036\000\023\000\
\024\000\012\000\012\000\016\000\017\000\018\000\022\000\031\000\
\021\000\032\000\033\000\019\000\006\000\021\000\034\000\011\000\
\037\000\000\000\000\000\000\000\017\000"

let yycheck = "\002\001\
\001\001\000\001\001\001\003\001\001\000\005\001\009\001\006\001\
\002\001\019\000\004\001\021\000\031\000\008\001\033\000\006\001\
\007\001\004\001\005\001\001\001\001\001\001\001\005\001\008\001\
\003\001\009\001\002\001\002\001\006\001\000\000\004\001\003\000\
\009\001\255\255\255\255\255\255\009\001"

let yynames_const = "\
  NEWLINE\000\
  COMMA\000\
  IF\000\
  DOT\000\
  QUERY\000\
  LPARAN\000\
  RPARAN\000\
  "

let yynames_block = "\
  ID\000\
  VAR\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 313 "ass4_parser.mly"
         ( )
# 400 "ass4_parser.ml"
               : unit))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : unit) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'hornclause) in
    Obj.repr(
# 314 "ass4_parser.mly"
                             ( )
# 408 "ass4_parser.ml"
               : unit))
; (fun __caml_parser_env ->
    Obj.repr(
# 317 "ass4_parser.mly"
                                    ( flush stdout )
# 414 "ass4_parser.ml"
               : 'hornclause))
; (fun __caml_parser_env ->
    Obj.repr(
# 318 "ass4_parser.mly"
                                    ( printf "syntax error!! \n"; flush stdout)
# 420 "ass4_parser.ml"
               : 'hornclause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'fact) in
    Obj.repr(
# 319 "ass4_parser.mly"
                                    ( printf " Fact added \n"; flush stdout)
# 427 "ass4_parser.ml"
               : 'hornclause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'rule) in
    Obj.repr(
# 320 "ass4_parser.mly"
                                    ( printf " Rule added \n"; flush stdout)
# 434 "ass4_parser.ml"
               : 'hornclause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'query) in
    Obj.repr(
# 321 "ass4_parser.mly"
                                    ( (answer _1 []); flush stdout )
# 441 "ass4_parser.ml"
               : 'hornclause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'atom) in
    Obj.repr(
# 325 "ass4_parser.mly"
                ( stack := !stack@[FACT(_1)])
# 448 "ass4_parser.ml"
               : 'fact))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'head) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'body) in
    Obj.repr(
# 327 "ass4_parser.mly"
                         ( stack := !stack@[RULE(_1,_3)] )
# 456 "ass4_parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'body) in
    Obj.repr(
# 329 "ass4_parser.mly"
                  (_1)
# 463 "ass4_parser.ml"
               : 'query))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 331 "ass4_parser.mly"
            ( _1 )
# 470 "ass4_parser.ml"
               : 'head))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 333 "ass4_parser.mly"
           ( _1::[] )
# 477 "ass4_parser.ml"
               : 'body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'body) in
    Obj.repr(
# 333 "ass4_parser.mly"
                                       ( _1::_3 )
# 485 "ass4_parser.ml"
               : 'body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'sterm) in
    Obj.repr(
# 335 "ass4_parser.mly"
                             ( (_1,_3) )
# 493 "ass4_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atomic) in
    Obj.repr(
# 337 "ass4_parser.mly"
             ( _1 )
# 500 "ass4_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'sterm) in
    Obj.repr(
# 337 "ass4_parser.mly"
                                            ( AT(_1,_3) )
# 508 "ass4_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 339 "ass4_parser.mly"
            ( [_1] )
# 515 "ass4_parser.ml"
               : 'sterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'sterm) in
    Obj.repr(
# 339 "ass4_parser.mly"
                                       ( _1::_3 )
# 523 "ass4_parser.ml"
               : 'sterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 341 "ass4_parser.mly"
                ( Id(_1) )
# 530 "ass4_parser.ml"
               : 'atomic))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 341 "ass4_parser.mly"
                                  ( Var(_1) )
# 537 "ass4_parser.ml"
               : 'atomic))
(* Entry input *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let input (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : unit)
;;
