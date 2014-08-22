type term = Id of string
          | Var of string
          | AT of string * (term list);;

type atom = string*(term list) ;;

type hornclause =   FACT of atom
              | RULE of atom * (atom list)
;;
type subst = (term * term) list;;