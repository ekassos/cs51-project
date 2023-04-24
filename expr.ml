(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
  | NegateFloat (* extension *)
  | Not (* extension *) ;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Over (* extension *)
  | Equals
  | DNE  (* extension *)
  | LessThan
  | GreaterThan (* extension *)
  | PlusFloat (* extension *)
  | MinusFloat (* extension *)
  | TimesFloat (* extension *)
  | OverFloat (* extension *) ;;

type varid = string ;;

type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* extension *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *) ;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var var -> SS.singleton var
  | Num _ | Bool _ | Float _ | Raise | Unassigned -> SS.empty
  | Unop (_u, e) -> free_vars e
  | Binop (_b, e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) -> SS.union (free_vars e1) (SS.union
    (free_vars e2) (free_vars e3))
  | Fun (var, e) -> SS.remove var (free_vars e)
  | Let (var, e1, e2) -> SS.union (free_vars e1) (SS.remove var (free_vars e2))
  | Letrec (var, e1, e2) -> SS.remove var (SS.union (free_vars e1) 
    (free_vars e2))
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2) ;;

(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)

let new_varname () :  varid =
  (* adapted from utilities.ml from pset 8 *)
  let gensym = 
    let ctr = ref 0 in
    fun () -> incr ctr;
              "var" ^ (string_of_int !ctr) in 
  gensym ();;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture  *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let subst' (e : expr) : expr = subst var_name repl e in 
    match exp with
    | Var var -> if var = var_name then repl else exp
    | Num _ | Bool _ | Float _ -> exp
    | Unop (u, e) -> Unop (u, subst' e)
    | Binop (b, e1, e2) -> Binop (b, subst' e1, subst' e2)
    | Conditional (e1, e2, e3) -> Conditional (subst' e1, subst' e2, subst' e3)
    | Fun (var, e) -> if var = var_name then exp
      else if SS.mem var (free_vars repl) then let y = new_varname () in 
      Fun (y, subst var (Var y) (subst' e)) else Fun (var, subst' e)
    | Let (var, e1, e2) -> if var = var_name then Let (var, subst' e1, e2)
      else if SS.mem var (free_vars repl) then let y = new_varname () in 
      Let (y, subst' e1, subst' (subst var (Var y) e2))
      else Let (var, subst' e1, subst' e2)
    | Letrec (var, e1, e2) -> if var = var_name then Letrec (var, e1, e2)
      else if SS.mem var (free_vars repl) then let y = new_varname () in 
      Letrec (y, subst y repl (subst var (Var y) e1), 
              subst y repl (subst var (Var y) e2))
      else Letrec (var, subst' e1, subst' e2)
    | Raise -> Raise
    | Unassigned -> Unassigned
    | App (e1, e2) -> App (subst' e1, subst' e2);;

(*......................................................................
  String representations of expressions
 *)

(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  (* helper functions adapted from expressionLibrary.ml of pset4 *)
  let unop_to_string (u : unop) : string =
    match u with
    | Negate -> "~-"
    | NegateFloat -> "~-."
    | Not -> "!" in 
  let binop_to_string (b : binop) : string =
    match b with
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Equals -> "="
    | LessThan -> "<"
    | GreaterThan -> ">"
    | Over -> "/"
    | PlusFloat -> "+."
    | MinusFloat -> "-."
    | TimesFloat -> "*."
    | OverFloat -> "/."
    | DNE -> "!=" in
  match exp with 
  | Var var -> var
  | Num num -> string_of_int num
  | Float num -> string_of_float num
  | Bool bool -> string_of_bool bool
  | Unop (u, e) -> unop_to_string u ^ exp_to_concrete_string e
  | Binop (b, e1, e2) -> exp_to_concrete_string e1 ^ " " ^ binop_to_string b ^
    " " ^ exp_to_concrete_string e2
  | Conditional (e1, e2, e3) -> "if " ^ exp_to_concrete_string e1 ^ " then " ^
    exp_to_concrete_string e2 ^ " else " ^ exp_to_concrete_string e3
  | Fun (var, e) -> "fun " ^ var ^ " -> " ^ exp_to_concrete_string e
  | Let (var, e1, e2) -> "let " ^ var ^ " = " ^ exp_to_concrete_string e1 ^
    " in " ^ exp_to_concrete_string e2
  | Letrec (var, e1, e2) -> "let rec " ^ var ^ " = " ^ exp_to_concrete_string e1
    ^ " in " ^ exp_to_concrete_string e2
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> exp_to_concrete_string e1 ^ " " ^ exp_to_concrete_string e2 
  ;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
(* helper functions adapted from expressionLibrary.ml of pset4 *)
  let unop_to_string (u : unop) : string =
    match u with
    | Negate -> "Negate"
    | NegateFloat -> "NegateFloat"
    | Not -> "Not" in 
  let binop_to_string (b : binop) : string =
    match b with
    | Plus -> "Plus"
    | Minus -> "Minus"
    | Times -> "Times"
    | Equals -> "Equals"
    | LessThan -> "LessThan"
    | GreaterThan -> "GreaterThan"
    | Over -> "Over"
    | PlusFloat -> "PlusFloat"
    | MinusFloat -> "MinusFloat"
    | TimesFloat -> "TimesFloat"
    | OverFloat -> "OverFloat"
    | DNE -> "DNE" in
  let parentheses (s1 : string) (s2: string) : string =
    s1 ^ "(" ^ s2 ^ ")" in 
  match exp with 
  | Var var -> parentheses "Var" var
  | Num num -> parentheses "Num" (string_of_int num)
  | Float num -> parentheses "Float" (string_of_float num)
  | Bool bool -> parentheses "Bool" (string_of_bool bool)
  | Unop (u, e) -> parentheses "Unop" (unop_to_string u ^ ", " ^ 
    exp_to_abstract_string e)
  | Binop (b, e1, e2) -> parentheses "Binop" (binop_to_string b ^ ", " ^ 
    exp_to_abstract_string e1 ^ ", " ^ exp_to_abstract_string e2)
  | Conditional (e1, e2, e3) -> parentheses "Conditional" 
    (exp_to_abstract_string e1 ^ ", " ^ exp_to_abstract_string e2 ^ ", " ^ 
    exp_to_abstract_string e3)
  | Fun (var, e) -> parentheses "Fun" (var ^ ", " ^ exp_to_abstract_string e)
  | Let (var, e1, e2) -> parentheses "Let" (var ^ ", " ^ 
    exp_to_abstract_string e1 ^ ", " ^ exp_to_abstract_string e2)
  | Letrec (var, e1, e2) -> parentheses "Letrec" (var ^ ", " ^ 
    exp_to_abstract_string e1 ^ ", " ^ exp_to_abstract_string e2)
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> parentheses "App" (exp_to_abstract_string e1 ^ ", " ^ 
    exp_to_abstract_string e2) ;;