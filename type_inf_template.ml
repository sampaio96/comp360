(* lexer and parser for the lambda calculus *)
(* from older programs *)
(* new stuff starts where it says *type inference* below *)

(* utility functions *)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l;;

let rec aux_print_list = function
  |[] -> print_string ""
  |(x::xs) -> (print_string x;print_string ":";aux_print_list xs);;

(* print list of strings *)
let print_list x =
  (print_string "<";aux_print_list x;print_string ">");;

(* lambda terms *)


(* type var = V of string *)

type term =
   TmVar of string
  |TmApp of (term * term)
  |TmAbs of (string * term)
  |TmTrue
  |TmFalse
  |TmIf of (term * term * term)
  |TmError


let rec show tm =
  match tm with
    |(TmVar x) -> x
    |(TmApp(t1,t2)) -> "("^(show t1)^" "^(show t2)^")"
    |(TmAbs(x,t)) -> "(\\"^x^"."^(show t)^")"
    |TmIf(t1,t2,t3) -> "(if "^(show t1)^" "^(show t2)^" "^(show t3)^")"
    |TmTrue -> "true"
    |TmFalse -> "false"
    |TmError -> "TM_ERROR";;


      (* lexer: breaks up a string into a list of tokens:
   "if true then false else (if true then false else true)" |-->
   ["if";"true";"then";"false";"else";"(";"if";"true";...]
      *)

let print_term t = print_string (show t)

(* char x is alphabetical *)
let alph x = 
  let n = Char.code x in
  94< n && n < 123 || 47<n && n <58;;


exception BAD_CHAR;;


(* token boundaries *)
let bdry x = (x='(') || (x= ')') || (x = '\\') || (x='.') || (x = '@');;

(* accumulate characters until you reach a blank or a token boundary:
'e' ['l';'s';'e';'(';...] |--> ("else" ['('...])
 *)
let rec grab_chars_until_bdry ch rest =
  match rest with
    |[] -> (String.make 1 ch,rest)  (* 'String.make 1 x' takes char x to string x *)
    |(head::tail) ->
       if (head = ' ')
       then (String.make 1 ch,tail)
       else if (bdry head)
       then (String.make 1 ch,rest)
       else let (x,l) = (grab_chars_until_bdry head tail)
       in
	 ((String.make 1 ch)^x,l)
;;

(* char list |--> list of token strings *)
let rec aux_lexx chars =
  match chars with
    |[] -> []
    |(ch::rest) ->
       if (ch=' ')
       then aux_lexx rest
       else if (bdry ch)
       then (String.make 1 ch)::(aux_lexx rest)
       else if (alph ch)
       then
	 let (str, remainder) = grab_chars_until_bdry ch rest
	 in str::(aux_lexx remainder)
       else (print_char ch;print_string": ";raise BAD_CHAR);;

let lexx x = aux_lexx (explode x);;
	
exception PAREN_EXCEPTION;;


  
(* messy parser to deal with:
  1.- eliminating left recursion in t-> x|\x.t|tt
  2.- left associativity of application 
input: a list of strings (output by lexx)
output (t,ls) where t is a term and ls is the remaining list of tokens 
that should be empty if the input represents a complete term
*)

  (* in an application sequence "t1 t2 t3 ..." parseOneL will 
   only parse the first term and return the remainder as a string list *)
let rec parseOneL lt =
  match lt with
  |[] -> (TmError,[])
  |("true"::rest) -> (TmTrue,rest)
  |("false"::rest) -> (TmFalse,rest)
  |("("::rest) ->
    let (tm',rest') = (parseL rest) in
	 if rest'=[]
	 then
	    (TmError,[])
	 else
	     let (rparen::after_paren) = rest' in
	   (tm',after_paren)
  |("\\"::rest) -> parseL lt    
  |("if"::rest) ->    let (t1,rest1) = parseOneL rest in
		   let (t2,rest2) = parseOneL rest1 in
		   let (t3,rest3) = parseOneL rest2 in
		   (TmIf(t1,t2,t3),rest3)
  |(")"::t) -> raise PAREN_EXCEPTION
  |(s::t) -> (TmVar(s),t)

  and
    (* parseL is the top-level parser *)
  parseL lt =
  match lt with
  |[] ->(TmError,[])
  |["true"] -> (TmTrue,[])
  |["false"] -> (TmFalse,[])
  |("true"::rest) -> aux_parseA TmTrue rest
  |("false"::rest) -> aux_parseA TmFalse rest    
  |("("::rest) ->  (* parenthesized term *)
    let (tm',rest') = (parseL rest) in
    if rest'=[]
    then
      (TmError,[]) (* error because there should have been at least a
   right parenthesis there*) 
    else
      let (rparen::after_paren) = rest' in
      aux_parseA tm' after_paren
  |("\\"::rest) -> (* abstraction *)
    let  (tok_var::after_var) = rest in
    let (tok_dot::after_dot) = after_var in
    let (tm,rest') = (parseL after_dot) in
    aux_parseA (TmAbs(tok_var,tm)) rest'
  |("if"::rest) -> let (t1,rest1) = parseOneL rest in
		   let (t2,rest2) = parseOneL rest1 in
		   let (t3,rest3) = parseOneL rest2 in
		   aux_parseA (TmIf(t1,t2,t3)) rest3
  |(s::t) -> aux_parseA (TmVar(s)) t (* single var or applocation *)
  and
    (* grabs terms one at a time and associates applications to the left *)
  aux_parseA tm lt =
  match lt with
  |[] -> (tm,[])
  |("true"::rest) -> aux_parseA (TmApp(tm,TmTrue)) rest
                    
  |("false"::rest) -> aux_parseA (TmApp(tm,TmFalse)) rest
  |("("::rest) -> 
    let (tm',rest') = parseOneL lt in
    aux_parseA (TmApp(tm,tm')) rest'
  |("\\"::rest) ->
    let (tm',rest') = parseL lt in
    aux_parseA (TmApp(tm,tm')) rest'
  |("if"::rest) -> let (tm',rest') = parseOneL lt in
		   aux_parseA (TmApp(tm,tm')) rest'
  |(")"::t) -> (tm,lt)
  |[s] -> (TmApp(tm,TmVar(s)),[])
  |(s::t) ->
    let (a::t') = t in
    if a=")"
    then (TmApp(tm,TmVar(s)),t)
    else aux_parseA (TmApp(tm,TmVar(s))) t
    
(* end parser *)		   

 	 
let parse text = fst (parseL (lexx text));;
let see_parse text = let (a,b) = parseL (lexx text) in
  (show a;print_string "--> ";print_list b);;

		       

(* counter for fresh variables *)
let x = ref 0;;

  


(* some definitions in the \-calculus *)
let lambda_if = parse "\\x.\\y.\\z.(x y z)";;
let lambda_tru = parse "\\x.\\y.x";;
let lambda_false = parse "\\x.\\y.y";;
let lambda_pair = parse "\\a.\\b.\\x.(x a b)";;
let lambda_succ = parse "\\n.\\s.\\z.(s (n s z))";;
let lambda_fst = parse "\\p.(p \\x.\\y.x)";;
let lambda_snd = parse "\\p.(p \\x.\\y.y)";;
let lambda_plus = parse "\\m.\\n.\\s.\\z.(m s (n s z))";;
let lambda_times = parse "\\m.\\n.\\z.(m (n z))";;
let lambda_iszero =
  TmAbs("m",TmApp(TmApp(TmVar "m",TmAbs("y",lambda_false)),lambda_tru)
       );;
  


(* boolean version of iszero. Must use it to get proper boolean answers *)

let iszerobool = parse "\\m.m (\\x.false) true";;



(* fixed point combinators *)
let curryfp = parse "\\f.(\\x.f (x x)) (\\x.(f (x x)))";;

let turingfp = parse "(\\z.\\f.f (z z f)) (\\z.\\f.(f (z z f)))";;

(* for call-by-value *)
let plotkinfp = parse "\\f.(\\x.f (\\y.x x y)) (\\x.f (\\y.x x y))";;



  (* ********************** type inference ******* *)



type lam = term

(* for type expressions *)
type arrow_type = Bool|Var of string|Arr of (arrow_type*arrow_type)

(* for typed lambda terms *)					      
type tylam = TyVar of string|TyApp of (tylam*tylam) |
    TyAbs of (string*arrow_type*tylam)




	       


(* convert type expressions into strings *)
let rec showtype ty =
  match ty with
    |Bool -> "Bool"
    |Var y -> y
    |Arr (t1,t2) -> "("^(showtype t1)^"->"^(showtype t2)^")"

(* convert typed lambda calculus terms to strings *)							   let rec showtylam tylm =
  match tylm with
    |TyVar y -> y
    |TyApp (t1,t2) -> "("^(showtylam t1)^" "^(showtylam t2)^")"
    |TyAbs (s,a,t) -> "("^"\\"^s^":"^(showtype a)^"."^(showtylam t)
		      ^")";;

(* convert contexts to strings *)
let rec show_ctx ctx =
  match ctx with
  |[] -> ""
  |[(x,tyx)] ->  x^":"^(showtype tyx)^" "
  |((x,tyx)::k) -> x^":"^(showtype tyx)^","^(show_ctx k)

(* create a judgment string
\Gamma |- t: T
 *)					      
let show_judgment ctx tytm ty =
  (show_ctx ctx)^" |- "^ (showtylam tytm)^" : "^(showtype ty)

(* equations *)
type eqn = Eq of (arrow_type*arrow_type)


(* convert equations to strings *)		   
let showeq eq =
  match eq with
    Eq(t1,t2) -> (showtype t1)^"="^(showtype t2)

(* convert lists of equations to strings *)				     
let rec showeq_list eqlist =
  match eqlist with
  |[] -> ""
  |[Eq(t1,t2)] -> showeq (Eq(t1,t2))
  |(e::es) -> (showeq e)^","^(showeq_list es)


(* manipulation of SUBSTITUTIONS *)
(* substitutions look like this:
[X1 -> T1,...,Xn->Tn]
formalize them as lists of pairs of terms
 *)
type subst =  (arrow_type*arrow_type) list

				     
(* showsub_aseq: (arrow_type*arrow_type) list -> string *)
(* turn substitutions into strings that look like this
x1 -> T1,...,Xn-> Tn
 *)				      
				      
let rec showsub_aseq sub =
  match sub with
  |[] ->""
  |[(Var x,ty)] ->  x^" = "^(showtype ty)
  |(Var x,ty)::rest -> x^" = "^(showtype ty)^","^(showsub_aseq rest)

	

exception FAIL

(* utility: member *)
let member x l = List.mem x l

(* get:arrow_type -> subst -> term
   apply only to type vars, and 
   retrieve value of var in sub
 *)
let rec get x s =
  match s with      
      [] -> x
    |(((Var y),tm)::ys) ->
       (match x with
	  | (Var z)  ->
	      if (z=y)
	      then tm
	      else get (Var z) ys)


(* apply:subst -> ty -> ty *)
(* This means apply a type-substitution to a type expression *)
let rec apply sub ty =
  match ty with
    | Bool -> Bool
    | (Var x) -> get (Var x) sub
    | (Arr(a1,a2)) -> Arr(apply sub a1,apply sub a2)

(* apply2term: subst -> tylam -> tylam *)			 
(* apply a type substitution to a typed lambda term *)
let rec apply2term sub tytm =
  match tytm with
  |(TyVar(x)) -> TyVar(x)
  |(TyApp(t1,t2)) -> TyApp(apply2term sub t1,apply2term sub t2)
  |(TyAbs(x,tyx,t)) -> let a = apply sub tyx in
		       let t' = apply2term sub t in
		       TyAbs(x,a,t')
			 
(* apply a subst to a list of equations *)

let apply_eq sub (Eq(t1,t2)) =
    Eq(apply sub t1, apply sub t2)

let rec  apply_to_list sub lst =
  match lst with
    |  [] -> []
    | (Eq(t1,t2)::rest) ->
	(apply_eq sub (Eq(t1,t2)))::(apply_to_list sub rest)


(* composition of substitutions *)

(* remove:term list -> sub -> sub
   use: remove (list_of_vars,subst) = subst with all 
         bindings for variables in the list_of_vars removed
  needed to compose two substitutions
 *)

let rec remove lst sub =
  match (lst,sub) with
    | ([],sub) -> sub
    | (list_of_vars, []) -> []
    | (list_of_vars, ((Var(y),tm):: bindings)) ->
	if member y list_of_vars
	then remove list_of_vars bindings
	else (Var y,tm)::(remove list_of_vars bindings)

(* composition of two substitutions *)

let rec domain lst =
  match lst with
    |[] -> []
    | ((Var y,t)::xs) -> y::(domain xs);;

(* remove_ids: sub -> sub
   remove all trivial bindings of the form (x,x)
*)
let rec remove_ids lst =
  match lst with
    |[] -> []
  | ((y,t)::xs) ->
    if y=t
    then remove_ids xs
    else ((y,t)::(remove_ids xs));;

(* apply_to_range: sub -> sub -> sub
   apply 2nd argument to values of bindings in 1st arg
  e.g. {(x1,t1),...} sub |===>  {(x1,t1 sub),...}
*)
let rec apply_to_range lst sub =
  match lst with
    |[] -> []
  | ((y,t)::xs) ->
    ((y,(apply sub t))::(apply_to_range sub xs));;


let rec compose sub1 sub2 =
  let dom = domain sub1 in
  let sub1_sub2_applied = apply_to_range sub1 sub2 in
  let clean_sub2 = remove dom sub2 in
  let s12 = sub1_sub2_applied@clean_sub2
  in
    remove_ids s12


(* occurs *)

let rec occurs x t =
  match (x,t) with
    |(Var z, Var u) -> z=u
    |(Var z, Arr(t1,t2)) -> occurs x t1 || occurs x t2
    |_ -> false
	 
(* unify a list of equations *)
let rec unify lst =
  match lst with
      [] -> 
    |(Eq(x,y)::rest) when x=y -> 
    | (Eq(Var(x),t)::rest) ->
    | (Eq(t,Var(x))::rest) ->
    | (Eq (Arr(a1,a2),Arr(b1,b2))::rest) ->

	  
let sub2string sub =
  "["^(showsub sub)^"]"

    

(* decorate untyped lambda terms with type variables *)


let x = ref 0 

let make_new_var () =
  x:=!x+1;
  "A"^(string_of_int !x)

let rec decorate tm =
  x:=0;
  match tm with
    |(TmVar y) -> (TyVar y)
    |(TmApp (t1,t2)) -> (TyApp (decorate t1,decorate t2))
    |(TmAbs (y,t)) -> (TyAbs (y,Var (make_new_var ()),(decorate t)));;

exception ARROW_TYPE_EXPECTED
exception VAR_NOT_IN_CONTEXT
exception ERROR of string
  
(* lookup the value of a variable in a context [(x,a),(y,b)...] *)
let rec look varstring ctx =
  match ctx with
    |[] -> raise (ERROR ("no type for "^varstring^" in context."))
    |((s,a)::rest) -> if (s=varstring) then a
      else look varstring rest;;

(* compute the type of a simply typed lambda term in a given context *)
	
let rec typeof ctx tylm =
  match tylm with
  |(TyVar y) -> look y ctx
  |(TyApp (t1,t2)) -> match typeof ctx t1 with
                      | Var(a) -> raise (ERROR ("application is not well typed"))
                      | Arr(a,b) -> let c = typeof ctx t2 in
                          if (a = c) then b else raise (ERROR ("application is not well typed"))
  |TyAbs (s,a,t) -> Arr(a,typeof (s,a)::ctx t)


	 
(*
make_constraints:
(string * arrow_type) list -> tylam -> arrow_type -> eqn list

takes a judgment: \Gamma |- tylam : ty  and generates a list of 
equations between types to be unified.
*)			     
let rec make_constraints ctx tylm ty =
  match tylm with
  |TyVar y -> Eq(typeof ctx y, ty)::[]
  |TyApp(t1,t2) -> let w = make_new_var in
                   let u1 = make_constraints ctx t1 Arr(Var(w), ty) in
                   let u2 = make_constraints ctx t2 Var(w) in
                   u1@u2
  |TyAbs(x,tyx,t) -> let w = make_new_var in
                     let u = make_constraints
                             (x, tyx) :: ctx
                             t
                             var(w) in
                     Eq(ty, Arr(Var(tyx),Var(w)))::u
 
  
let t1 = parse "\\x.\\y.x y" in
    let t2 = decorate t1 in
    let u = make_constraints [] t2 (Var("A")) in
    let u' = unify u in
    let t' = apply2term u' t2 in
    (showtylam t',showtype (typeof [] t'));;
    
let type_inf ctx str =
  let t1 = parse str in
  let t2 = decorate t1 in
  let u = make_constraints [] t2 (Var("A")) in
  let u' = unify u in
  let t' = apply2term u' t2 in
  show_judgment ctx t' (typeof ctx t');;
		     
  
  (* tests *)

type_inf [] "\\x.\\y.\\z.(x z)(y z)";;
  
  type_inf [] "\\x.x x";;

    type_inf [] "\\x.\\y.y(x y)";;

      type_inf [] "\\x.\\y.(y x) y";;
