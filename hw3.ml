(* TEMPLATE FOR evaluating lambda+bool calculus *)
(* included: lexer + parser and small-step evaluators for 
 *lambda-calc+booleans, both
 * normal order and call-by-value 
 * MISSING: substition and big-step evaluators for both strategies and *)
(* some utility functions 
*)

(* required: implementation of 


-- subst
-- is_a_nf (determines whether or not a term is in normal form)
-- is_val (determines whether or not a term is a VALUE, i.e. an abstraction)
-- big_step_cbv

You only have to complete those pieces of code where it says 
'to be completed by YOU


FOR Extra credit: (OPTIONAL)

--implementation of big_step: this would be a big_step evaluator for 
normal-order reduction. This requires you to work out the big-step 
rules for normal order first, then implement it. In order to do this
you need to use 
-- is_a_nf:tm -> bool
that determines whether a lambda term is in normal form

If you choose not to do the optional parts remember to comment them
out so you can run this file

At the bottom of the file are several examples using the factorial,
defined in different ways. They should run and return the right
answers.
 *)


(* lexer, parser and normal-order evaluator for the untyped lambda calculus + booleans*)
(* uses a single reference variable to keep track of fresh-variable renaming *)
(* note that 'if' has been reduced to a single word: no 'then', 'else' *)

(* concrete syntax
   lam -> x|lam lam|\\x.lam

right-recursive equiv

lam -> x tail|\\x.lam tail
tail -> lam tail |epsilon

after epsilon-production-removal

lam -> x|x tail|\\x.lam | \\x.lam tail
tail -> lam | lam tail

   abstract syntax
   tm-> TmVar(string)|TmApp(tm,tm)|TmAbs(string,tm)

To this we add a lazy if
tm -> if tm tm tm |false|true
(I dropped the 'then' and 'else')

abstract syntax
tm -> TmIf(tm,tm,tm)|TmTrue|TmFalse
*)


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


type term =
   TmVar of string
  |TmApp of (term * term)
  |TmAbs of (string * term)
  |TmTrue
  |TmFalse
  |TmIf of (term * term * term)
  |TmError (* for debugging *)

     

(* show:term -> string *)
let rec show tm =
  match tm with
    |(TmVar x) -> x
    |(TmApp(t1,t2)) -> "("^(show t1)^" "^(show t2)^")"
    |(TmAbs(x,t)) -> "(\\"^x^"."^(show t)^")"
    |TmIf(t1,t2,t3) -> "(if "^(show t1)^" "^(show t2)^" "^(show t3)^")"
    |TmTrue -> "true"
    |TmFalse -> "false"
    |TmError -> "TM_ERROR";;

  (* display_term: term -> string. shows term in *)
(* abstract syntax form *)
let rec display_term tm =
   match tm with
    |(TmVar x) -> "TmVar"^"("^x^")"
    |(TmApp(t1,t2)) -> "TmApp("^(display_term t1)^","^(display_term t2)^")"
    |(TmAbs(x,t)) ->  "TmAbs("^x^","^(display_term t)^")"
    |TmIf(t1,t2,t3) -> "TmIf("^(display_term t1)^","^(display_term t2)^","^
			 (display_term t3)^")"
    |TmTrue -> "true"
    |TmFalse -> "false"
    |TmError -> "TM_ERROR";;

(* dt: term -> unit. Has side effect of printing the term in abstract *)
(* syntax string form *)
let dt tm = print_string(display_term tm);;
  
 

(* lexer: breaks up a string into a list of tokens:

   \\x1.(\\x2.x1 x2) x1 |-->
   ["\\";"x1";".";"(";"\\";"x2";".";"x1";"x2";")";"x1"]
 *)

let print_term t = print_string (show t);;

(* test whether char x is alphabetical *)
let alph x = 
  let n = Char.code x in
  94< n && n < 123 || 47<n && n <58;;


exception BAD_CHAR;;


(* token boundaries *)
let bdry x = (x='(') || (x= ')') || (x = '\\') || (x='.');;

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

(* end lexer *)

  
exception PAREN_EXCEPTION;;


  
(* messy PARSER to deal with:
  1.- eliminating left recursion in t-> x|\x.t|tt
  2.- left associativity of application: x y z means ((x y) z)
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
  |(")"::t) -> raise PAREN_EXCEPTION (* for debugging *)
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
    (* grabs terms in an application one at a time and associates applications to the left *)
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
    if a=")" (* you reached the end of an application sequence *)
    then (TmApp(tm,TmVar(s)),t)
    else aux_parseA (TmApp(tm,TmVar(s))) t
    


 	 
let parse text = fst (parseL (lexx text));;
let see_parse text = let (a,b) = parseL (lexx text) in
  (show a;print_string "--> ";print_list b);;

(* end parser *)

  

(* substitution into lambda terms *)

(* utility. Included just for fun. You don't need these. *)
let rec member x lst =
  match lst with
      [] -> false
    |(y::ys) -> x=y || member x ys;;

let rec elim_reps = function
  |[] -> []
  |(x::xs) -> if member x xs
    then elim_reps xs
    else x::(elim_reps xs);;

let rec union l1 l2 = elim_reps(l1@l2);;

(* return list lst with all occurrences of 'x' removed *)
let rec delete x lst =
  match lst with
      [] -> []
    |(y::ys) -> if (x=y)
      then delete x ys
      else y::(delete x ys);;
      

(* free_vars: term -> string list *)
let rec free_vars t =
  match t with
    |TmVar s -> [s]
    |TmAbs(x,t) -> let fvlist = free_vars t in
	delete x fvlist
    |TmApp(t1,t2) -> union (free_vars t1) (free_vars t2)
    |TmIf(t1,t2,t3)
     -> union (free_vars t1) (union (free_vars t2) (free_vars t3));;
(* end utility *)

(* rename free variables. newname is to be a fresh name.
   Therefore capture cannot occur, so we do not consider the problem.
    i.e. reame name newname tm REPLACES every free occurrence of name 
   by newname in tm, without trying to avoid capture. It must be used to
   define subst.
   rename:string -> string -> term -> term
 *)
let rec rename name newname tm =
  match tm with
  |TmTrue -> TmTrue
  |TmFalse -> TmFalse
  |TmVar s -> if(s=name)
      then TmVar newname
      else TmVar s
    |TmApp(t1,t2) ->
       TmApp(rename name newname t1, rename name newname t2)
    |TmAbs(x,t) ->
       if(x=name) then TmAbs(x,t)
       else TmAbs(x,rename name newname t)
    |TmIf(t1,t2,t3) ->
      let t1' = rename name newname t1 in
      let t2' = rename name newname t2 in
      let t3' = rename name newname t3 in
      TmIf(t1',t2',t3')
		       

(* counter for fresh variables *)
let x = ref 0;;

  
(* used to generate fresh variable name: uses assignment *)
let make_fresh_var () =
  x := !x+1;
  "_x"^(string_of_int !x);;
	 
	

(* substition:
subst:string -> term -> term -> term
computes the result of substituting 's' (a term) for TmVar(var) in 'term'
AVOIDING CAPTURE
 *)
(* to be completed by YOU *)
let rec subst var s term =
  match term with
  |TmTrue -> TmTrue
  |TmFalse -> TmFalse
  |TmVar y -> if (y=var)
	      then s
	      else term
  |TmApp(t1,t2) -> TmApp(subst var s t1, subst var s t2)
  |TmAbs(y,t) -> if (y=var) 
               then term
               else 
               let newvar = make_new_var() in
               let ren = rename(y, newvar, t) in
               TmAbs(newvar, subst var s ren)

                (* here is where you must avoid capture by generating *)
                (* a new var and renaming. Remember to check if y=var *)
    
  |TmIf(t1,t2,t3) -> TmIf(subst var s t1, subst var s t2, subst var s t3)

  


(* Call By Value *)

exception NO_RULE;;
exception NO_RULE1;;
  
exception BAD_GUARD;;

(* is a value*)
(* is_val: term -> bool *)
(* to be completed by YOU *)
let is_val tm =

  (* computes one step of evaluation using call-by-value rules *)
let rec eval_step_cbv t =
  match t with
  | TmIf(TmTrue,t1,t2) -> t1 (*lazy if *)
  | TmIf(TmFalse,t1,t2) -> t2
  | TmIf(b,t1,t2) -> let b' = eval_step_cbv b in
		     TmIf(b',t1,t2)			    
  | TmApp (TmAbs (x,t1),t2) when is_val t2 -> subst x t2 t1
  | TmApp (t1,t2) when is_val t1 -> TmApp (t1, eval_step_cbv t2)
  | TmApp (t1,t2) -> TmApp (eval_step_cbv t1, t2)
  | _ -> raise NO_RULE;;

(* eval_cbv 
 * a value is an abstraction
 * *)
let rec cbv_eval t = if is_val t then t else cbv_eval (eval_step_cbv t);;


(* resets the free-variable counter to 0 before evaluating *)
let top_cbv_eval t =
  x:= 0;
  cbv_eval t



(* Normal order *)

(* tests whether or not input term is in normal form: to be completed by YOU.
TmTrue,TmFalse are considered normal forms *)
	   
let rec is_a_nf tm = 
  match tm with
  |TmTrue -> 
  |TmFalse ->
  |TmIf(v,_,_) -> (* only a normal form if v is a normal form and is
  NOT true or false, i.e. it's garbage *) 
  |TmVar( _ ) ->
  |TmApp(TmAbs(_,_),_) 
  |TmApp(v,w) -> (* careful *)
  |TmAbs(_,t) -> 


  exception TM_ERROR
  (* one evaluation step in normal order *)
let rec no_step tm = 
  match tm with
  (* you can delete the first two lines if you want, they don't 
   * really help *)
  |TmTrue -> raise TM_ERROR
  |TmFalse -> raise TM_ERROR
  |TmIf(TmTrue,t1,t2) -> t1
  |TmIf(TmFalse,t1,t2) -> t2
  |TmIf(b,t1,t2) -> let b' = no_step b in
		    TmIf(b',t1,t2)			   
  |TmAbs(x,t) ->
    let t' = no_step t in
    TmAbs(x,t')
  |TmApp(TmAbs(x,t),u) ->
    subst x u t
  |TmApp(t1,t2) ->  (* t1 is not an abstraction: else this would have
  matched the preceding line *)
    if (is_a_nf t1)  
    then let t2'=no_step t2 in
	 TmApp(t1,t2')
    else
      let t1' = no_step t1 in
      TmApp(t1',t2)
  |v -> (print_string "===> ";print_string (show v);print_string "\n";raise NO_RULE);;

(* normal order evaluation *)
let rec no_eval t =
  if(is_a_nf t)
  then t
  else let t'=no_step t in
       no_eval t';;


(* resets fresh variable counter at start of computation *)
let top_no_eval t =
  x := 0;
  no_eval t;;



 
(* big step: TO BE COMPLETED BY YOU *)
(* normal order *)

let non_abstraction t =
  match t with
  |TmAbs(_,_) -> false
  |v -> true;;

(* normal order *)
(* remember to handle the booleans TmIf,TmTrue,TmFalse *)
let rec big_step t =
  match t with 
   TmIf (t1,t2,t3) -> 
  |TmTrue -> TmTrue
  |TmFalse -> TmFalse
  |TmAbs(s,t)-> TmAbs(x,y)
  |TmApp (t1, t2) -> 

(* resets free-variable counter to 0 before evaluating big_step cbv *)
let top_big_step t =
  x := 0;
  big_step t;;
  
(* call-by-value big step: TO BE COMPLETED BY YOU *)
(* remember to handle the booleans TmIf,TmTrue,TmFalse *)    
let rec big_step_cbv t =
  match t with
   TmTrue -> TmTrue
  |TmFalse -> TmFalse
  |TmIf (t1,t2,t3) -> 
  |TmAbs(s,t)-> TmAbs(x,y)
  |TmApp (t1, t2) -> 

 

(* resets free-variable counter to 0 before evaluating big_step cbv *)
let top_big_step_cbv t =
  x := 0;
  big_step_cbv t;;

(* end of material to be completed *)
  
(* material below included to define a lot of 'famous' lambda terms
so you can run the examples *)

(* compute with Church numerals *)
let rec make_num_body x =
  match x with
    |0 -> TmVar "z"
    |n -> TmApp(TmVar "s",make_num_body (n-1));;

let num2church x = TmAbs("s",TmAbs("z",make_num_body x));;

exception BAD_NUMERAL;;

(* convert Church numerals to integers *)
let rec translate_church_body s z x =
  match x with
    |TmVar(z) -> 0
    |(TmApp(f,t))  when (f=TmVar(s)) -> 1+(translate_church_body s z t)
    |_ -> raise BAD_NUMERAL;;

let church2num x =
  let x' = no_eval x in
  match x' with
  |(TmAbs(s,TmAbs(z,t))) -> make_church_body s z t
  |_ -> raise BAD_NUMERAL;;


(* create +t1 t2 term in lambda caluclus *)
let makeplus t1 t2 =
  let t1' = num2church t1 in
  let t2' = num2church t2 in 
  let text_plus = "\\m.\\n.\\s.\\z.((m s) ((n s) z))" in
  let plus = parse text_plus in
    TmApp(TmApp(plus,t1'),t2');;

(* create * t1 t2 term in \-calculus *)
let maketimes t1 t2 =
  let t1' = num2church t1 in
  let t2' = num2church t2 in 
  let text_times = "\\m.\\n.\\z.(m (n z))"
  in let times = parse text_times in
    TmApp(TmApp(times, t1'),t2');;
	     
       

(***************)

(* create the term (exp t1 t2) *)
let makexp t1 t2 =
  let t1' = num2church t1 in
  let t2' = num2church t2 in
    TmApp(TmApp (TmAbs("x",TmAbs("y",TmApp(TmVar "y",TmVar "x"))),t1'),t2');;
	     

(* create (succ t) *)
let makesucc t =
  let t' = num2church t in
  let succ = (parse "\\n.\\s.\\z.(s ((n s) z))") in
    TmApp(succ,t');;

(* fixed point combinators *)
let curryfp = parse "\\f.(\\x.f (x x)) (\\x.(f (x x)))";;

let turingfp = parse "(\\z.\\f.f (z z f)) (\\z.\\f.(f (z z f)))";;

let plotkinfp = parse "\\f.(\\x.f (\\y.x x y)) (\\x.f (\\y.x x y))";;  (* for call-by-value *)


(* some definitions in the \-calculus to play with *)
let lambda_if = parse "\\x.\\y.\\z.(x y z)";; (* DO NOT use in CBV, use 'if' *)
let lambda_tru = parse "\\x.\\y.x";;
let lambda_false = parse "\\x.\\y.y";;
let lambda_pair = parse "\\a.\\b.\\x.(x a b)";;
let lambda_succ = parse "\\n.\\s.\\z.(s (n s z))";;
let lambda_fst = parse "\\p.(p \\x.\\y.x)";;
let lambda_snd = parse "\\p.(p \\x.\\y.y)";;
let lambda_plus = parse "\\m.\\n.\\s.\\z.(m s (n s z))";;
let lambda_times = parse "\\m.\\n.\\z.(m (n z))";;
let lambda_iszero = TmAbs("m",TmApp(TmApp(TmVar "m",TmAbs("y",lambda_false)),lambda_tru));;
(* predecessor for church numerals *)
let lambda_zz = TmApp(TmApp(lambda_pair,num2church 0),num2church 0);;
let lambda_ss = TmAbs("p",TmApp(TmApp(lambda_pair,TmApp(lambda_snd,TmVar "p")),TmApp(TmApp(lambda_plus,(num2church 1)),TmApp(lambda_snd,TmVar "p"))));;
let lambda_pred = TmAbs("m",TmApp(lambda_fst,TmApp(TmApp(TmVar "m",lambda_ss),lambda_zz)));;

(* boolean versions *)

let iszerobool = parse "\\m.m (\\x.false) true";;


let body_fact = TmAbs("w",TmAbs("x",TmIf(TmApp(iszerobool,TmVar "x"),
					 (num2church 1),
					 TmApp(TmApp(lambda_times,TmVar "x"),
					       TmApp(TmVar "w",TmApp(lambda_pred,TmVar "x"))))));;
(* Three versions of the factorial with different fixed point combinators *)
let fact = TmApp(turingfp,body_fact);;
let fact_cbv = TmApp(plotkinfp,body_fact);;
let factY = TmApp(curryfp,body_fact);;

(* factorial: int -> int using three different fixed point combinators 
 * with different reduction  strategies
*)
let factorial n = church2num (top_no_eval (TmApp(fact,num2church n)));;
let factorial_cbv n = church2num (top_cbv_eval (TmApp(fact_cbv,num2church n)));;
let factorialY n = church2num (top_no_eval (TmApp(factY,num2church n)));;

let times m n = church2num (top_no_eval (TmApp(TmApp(lambda_times,num2church m),num2church n)));;
let exp n1 n2 = church2num (top_no_eval (makexp n1 n2));;



(* utilities. Just here for fun *)
(* tests whether 'x' occurs freely in t *)
let rec occurs_freely x t =
  match t with
    |TmVar(y) -> x = y
    |TmApp(t1,t2) -> (occurs_freely x t1) || (occurs_freely x t2)
    |TmAbs(y,t) -> if (x=y) then false
      else (occurs_freely x t)

(* returns list of bound variables *)	     
let rec bvars t =
  match t with
    |TmVar y -> []
    |TmApp(t1,t2) ->  (bvars t1) @ (bvars t2)
    |TmAbs(x, t) -> if (occurs_freely x t)
      then (x:: (bvars t))
      else bvars t;;

(* apply t to x 'n' times *)
let rec app n t x =
  match n with
  |0 -> x
  |m -> (t (app (n-1) t x));;

  


  (* tests *)
  times 6 7;;
    exp 2 3;;
  factorial 4;;
    factorial_cbv 4;;
      factorialY 4;;


(* using big-step *)
	    let big_step_factorial n =
	      (church2num (big_step (TmApp(factY,num2church n))));;
(* using call-by-value big-step *)
	    let big_step_cbv_factorial n =
	      (church2num (big_step_cbv (TmApp(fact_cbv,num2church n))));;

(* tests *)
	      big_step_factorial 4;;
		big_step_cbv_factorial 4;;
	    
	  
	
		  
