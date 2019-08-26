(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	         
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(************************** Start of our code **********************************)
(*Check that there are no duplications in a given list*)
let isUnique list = 
  let withoutDuplicates = List.sort_uniq (String.compare) list in
  if ((List.compare_lengths withoutDuplicates list) == 0)
  then list
  else raise X_syntax_error

(*Checks that var is not reserved word*)
let isReservedWord x = 
  let isReserved = List.mem x reserved_word_list in
  if (isReserved) 
  then raise X_syntax_error
  else Var(x);;

let rec tag_parse = function
  (*Constants*)
  | Number(x)-> Const(Sexpr(Number(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | String(x)-> Const(Sexpr(String(x)))
  | Pair(Symbol("quote"), Pair(x, Nil))-> Const(Sexpr(x))
  (*QQ*)
  | Pair(Symbol("quasiquote"), Pair(x, Nil))-> tag_parse (expandQQ x)
  (*Variables*)
  | Symbol(x) -> isReservedWord x
  (*Conditionals*)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)   (*if then else*)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parse test, tag_parse dit, Const (Void))   (*if then*)
  (*Begin*)
  | Pair(Symbol("begin"), x) -> buildSeq x true (*Explict Seq*)
  (*Set!*)
  | Pair(Symbol("set!"), Pair(Symbol(var), Pair(value, Nil))) -> Set(tag_parse (Symbol(var)), tag_parse value)
  (*MIT Define*)
  | Pair(Symbol("define"), Pair(Pair(Symbol(name), args), body)) -> Def(tag_parse (Symbol(name)), tagLambda args body) 
  (*Define*)
  | Pair(Symbol("define"), Pair(Symbol(var), Pair(value, Nil))) -> Def(tag_parse (Symbol(var)), tag_parse value)
  (*Or*)
  | Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool(false)))
  | Pair(Symbol("or"), Pair(x, Nil)) -> tag_parse x
  | Pair(Symbol("or"), x) -> Or (foldPairs x)
  (*And*)
  | Pair(Symbol("and"), Nil) -> Const(Sexpr(Bool(true)))
  | Pair(Symbol("and"), args) -> expandAnd args
  (*Lambdas*)
  | Pair(Symbol("lambda"), Pair(arg_list , exprplus))-> tagLambda arg_list exprplus
  (*Let*)
  | Pair(Symbol("let"), Pair(Nil, body)) -> expandLet (Pair(Nil,Nil)) body   (*empty let*)
  | Pair(Symbol("let"), Pair(Pair(rib, ribs), body)) -> expandLet (Pair(rib, ribs)) body
  (*LetStar*)
  | Pair(Symbol("let*"),Pair(Nil,body))-> expandLet (Pair(Nil,Nil)) body (*empty letstar*)
  | Pair(Symbol("let*"), Pair(Pair(rib, Nil), body)) -> expandLet (Pair(rib, Nil)) body
  | Pair(Symbol("let*"), Pair(Pair(rib, ribs), body)) -> tag_parse (Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair(ribs, body)), Nil))))
  (*Letrec*)
  | Pair(Symbol("letrec"), Pair(Nil, body)) ->  expandLet (Pair(Nil,Nil)) body   (*empty letrec*)
  | Pair(Symbol("letrec"), Pair(Pair(rib, ribs), body)) -> tag_parse (Pair(Symbol("let"), Pair(fakeInit (Pair(rib, ribs)), (buildLetrecBody (Pair(rib, ribs)) body))))
  (*Cond*)
  | Pair(Symbol("cond"), ribs) -> tag_parse (expandCond ribs)
  (*Applic*)  
  | Pair(name, args) -> Applic(tag_parse name, tagApplicArgs args)
  | _ -> raise X_syntax_error

and expandQQ = function
  | Nil -> (Pair(Symbol("quote"), Pair(Nil, Nil)))
  | Pair(Symbol("unquote"), Pair(x, Nil)) -> x
  | Pair(Symbol("unquote-splicing"), Pair(x, Nil)) -> raise X_syntax_error  
  | Vector(x) -> Pair(Symbol("vector"), listToNestedPairs (List.map expandQQ x))
  | Pair(Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)), cdr) -> Pair(Symbol("append"), Pair(sexpr, Pair(expandQQ cdr, Nil)))
  | Pair(car, Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil))) -> Pair(Symbol("cons"), Pair(expandQQ car, Pair( sexpr, Nil)))
  | Pair(car,cdr) -> Pair(Symbol("cons"), Pair(expandQQ car, Pair(expandQQ cdr,Nil)))  
  | x -> Pair((Symbol("quote")), Pair(x, Nil))

and listToNestedPairs list = List.fold_right (fun hd tl -> Pair(hd, tl)) list Nil

and expandCond = function
  | Pair(Pair(expr, Pair (Symbol("=>"), exprf)), Nil) -> 
  Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(expr, Nil)), 
  Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, exprf)), Nil)), Nil)), 
  Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))), Nil)))
  | Pair(Pair(expr, Pair (Symbol("=>"), exprf)), otherRib) ->   
  Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(expr, Nil)), 
  Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, exprf)), Nil)),
  Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(expandCond otherRib, Nil))), Nil)), Nil))),
  Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil)))
  | Pair(Pair(Symbol("else"), Nil), _) -> raise (*InvalidSeq*) X_syntax_error
  | Pair(Pair(Symbol("else"), exprs), Nil) -> Pair(Symbol("begin"), exprs)
  | Pair(Pair(exprTest, Nil), _) -> raise (*InvalidSeq*) X_syntax_error
  | Pair(Pair(exprTest, rest), Nil) -> Pair(Symbol("if"), Pair(exprTest, Pair(Pair(Symbol("begin"), rest), Nil)))
  | Pair(Pair(exprTest, rest), otherRib) -> Pair(Symbol("if"), Pair(exprTest, Pair(Pair(Symbol("begin"), rest), Pair(expandCond otherRib, Nil))))
  | _ -> raise X_syntax_error

and buildLetargs  = function
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), Nil) -> Pair(Symbol(x), Nil)
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), rest) -> Pair(Symbol(x), (buildLetargs rest))
  | _ -> raise X_syntax_error

(*(rib, ribs) must be proper list. Get all ribs*)
and buildLetParamsToApply  = function
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), Nil) -> Pair(sexpr, Nil)
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), rest) -> Pair(sexpr, (buildLetParamsToApply rest))
  | _ -> raise X_syntax_error

(*functions for letrec*)
and fakeInit = function
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), Nil) -> Pair(Pair(Symbol(x), Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), Nil)
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), rest) -> Pair(Pair(Symbol(x), Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), fakeInit rest)
  | _ -> raise X_syntax_error

and buildLetrecBody ribs body = match ribs with
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), Nil) -> Pair(Pair(Symbol("set!"), Pair(Symbol(x), Pair(sexpr, Nil))), body)
  | Pair(Pair(Symbol(x), Pair(sexpr, Nil)), rest) -> Pair(Pair(Symbol("set!"), Pair(Symbol(x), Pair(sexpr, Nil))), buildLetrecBody rest body)
  | _ -> raise X_syntax_error
(*end of functions for letrec*)  

and expandLet ribs body = 
  if (ribs = Pair(Nil,Nil))
  then Applic ((tagLambda Nil body), tagApplicArgs Nil)
  else 
  let letArgs = buildLetargs ribs in
  let letParamsToApply = buildLetParamsToApply ribs in 
  Applic ((tagLambda letArgs body), tagApplicArgs letParamsToApply)

and tagLambda arg_list exprplus =
  let body = buildSeq exprplus false in
  if (arg_list = Nil)
  then 
  let params = [] in 
  LambdaSimple(params, body)
  (*end of then*)
  else 
    try let params = isUnique (buildProperList arg_list) in 
    LambdaSimple(params, body)
  (*end of else*)  
  with X_syntax_error ->
    let params = buildImproperList arg_list in
    let params = isUnique params in 
    let lastParam = List.nth params ((List.length params)-1) in
    let firstParams = List.rev (List.tl (List.rev params)) in
    LambdaOpt(firstParams, lastParam , body)

and tagApplicArgs args = match args with
  | Nil -> []
  | _ -> foldPairs args

and expandAnd = function
  | Pair(hd, Nil) -> tag_parse hd
  | Pair(hd, tl) -> If(tag_parse hd, expandAnd tl, tag_parse (Bool false))
  | x -> tag_parse x

and buildSeq seq isExplicit = match seq, isExplicit with
  | Nil, true -> Const (Void)
  | Nil, false -> raise X_syntax_error         (*Implict seqs cannot be empty*)
  | Pair(Nil,Nil), _ -> raise X_syntax_error   (*according to SCM, can't type (begin ())*)
  | Pair(x, Nil), _-> tag_parse x
  | x, _ -> Seq(foldPairs x)

(*Gets nested pairs and builds List of sexprs*)
and foldPairs  = function
  | Pair(x,Nil) -> tag_parse x :: []
  | Pair(x, r) -> tag_parse x ::(foldPairs r)
  | _ -> raise X_syntax_error

(*Get nested pairs (with nil and the end) and builds List*)
and buildProperList  = function
  | Pair(Symbol(x), Nil) -> x :: []
  | Pair(Symbol(x), r) -> x :: (buildProperList r)
  | _ -> raise X_syntax_error

(*Get nested pairs (without nil and the end) and builds List*)
and buildImproperList  = function
  | Symbol(x) -> x :: []
  | Pair(Symbol(x), r) -> x :: (buildImproperList r)
  | _ -> raise X_syntax_error;;

(************************** Start of our code **********************************)

let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse sexpr;;

end;; (* struct Tag_Parser *)


