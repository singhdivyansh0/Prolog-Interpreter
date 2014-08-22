%{
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

  
%}  

/*--------------------------------------------------------------------------------------------------------------------------*/
/* GRAMMAR */

%token NEWLINE
%token COMMA 
%token IF
%token DOT
%token QUERY
%token <string> ID
%token <string> VAR
%token LPARAN RPARAN

%start input
%type <unit> input

%% 
input:   { }
        | input hornclause   { }
;

hornclause:     NEWLINE             { flush stdout }
              | error NEWLINE       { printf "syntax error!! \n"; flush stdout}
              | fact NEWLINE        { printf " Fact added \n"; flush stdout}
              | rule NEWLINE        { printf " Rule added \n"; flush stdout}
              | query NEWLINE       { (answer $1 []); flush stdout }
;


fact:  atom DOT { stack := !stack@[FACT($1)]}

rule:  head IF body DOT  { stack := !stack@[RULE($1,$3)] }

query: body QUERY {$1}

head:  atom { $1 };

body: atom { $1::[] }| atom COMMA body { $1::$3 };

atom: ID LPARAN sterm RPARAN { ($1,$3) };

term: atomic { $1 }| ID LPARAN sterm RPARAN { AT($1,$3) };        

sterm: term { [$1] }| term COMMA sterm { $1::$3 };          

atomic:   ID    { Id($1) }| VAR   { Var($1) };

%%