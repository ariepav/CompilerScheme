(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | Box'(_), Box'(_) -> true
  | BoxGet'(_), BoxGet'(_) -> true
  | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
  | _ -> false;;
	                  
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct
  
(********************************* our code starts here *********************************)

let rec convertToExprTag varTable e = match e with
  | Const(x) -> Const'(x)
  | Var(x) -> Var'(findVar varTable x (-1))
  | If(test,dit,dif) -> If'(convertToExprTag varTable test, convertToExprTag varTable dit,convertToExprTag varTable dif)
  | Seq(exprList) -> Seq'(List.map (convertToExprTag varTable) exprList)
  | Set(expr1,expr2) -> Set'(convertToExprTag varTable expr1, convertToExprTag varTable expr2)
  | Def(expr1,expr2) -> Def'(convertToExprTag varTable expr1, convertToExprTag varTable expr2)
  | Or(exprList) -> Or'(List.map (convertToExprTag varTable) exprList)
  | LambdaSimple(stringList, expr) -> LambdaSimple'(stringList, convertToExprTag (stringList :: varTable) expr)
  | LambdaOpt (stringList, string, expr) -> LambdaOpt' (stringList, string, convertToExprTag ((stringList @ [string]) :: varTable) expr)
  | Applic(expr, exprList) -> Applic'(convertToExprTag varTable expr, List.map (convertToExprTag varTable) exprList)

and findVar varTable x major = match varTable with
  | [] -> VarFree(x)
  | head :: tail ->
      let minor  = getMinor x head 0 in
      if (major = -1) && (minor != -1)
      then VarParam(x, minor)
      else if (major != -1) && (minor != -1)
      then VarBound(x, major, minor)
      else findVar tail x (major+1)

and getMinor x list i = match list with
  | [] -> -1
  | head :: tail -> if (x = head) then i else (getMinor x tail (i+1));;

let rec convertToApplicTP inTP e = match e with
  | Const'(x) -> Const'(x)
  | Var'(x) -> Var'(x)
  | If'(test,dit,dif) -> If'(convertToApplicTP false test, convertToApplicTP inTP dit, convertToApplicTP inTP dif)
  | Seq'(exprList) -> Seq' (seqTag exprList inTP)
  | Set'(expr1,expr2) -> Set'(expr1, convertToApplicTP false expr2)
  | Def'(expr1,expr2) -> Def'(expr1, convertToApplicTP false expr2)
  | Or'(exprList) -> Or'(seqTag exprList inTP)
  | LambdaSimple'(stringList, expr) -> LambdaSimple'(stringList, convertToApplicTP true expr)
  | LambdaOpt' (stringList, string, expr) -> LambdaOpt' (stringList, string, convertToApplicTP true expr)
  | Applic'(expr, exprList) -> if inTP = true then ApplicTP'(convertToApplicTP false expr, List.map (convertToApplicTP false) exprList) else Applic'(convertToApplicTP false expr, List.map (convertToApplicTP false) exprList)
  | _ -> convertToApplicTP inTP e (*Should never happen*)

and seqTag list inTP = 
  let r = List.rev list in
  let lastExp = List.hd r in
  let otherExprs = List.rev (List.tl r) in
  let tagged = (List.map (convertToApplicTP false) otherExprs) @ [(convertToApplicTP inTP lastExp)] in
  tagged;;

let ribNumber = ref 0;; (*a pointer that indicates if there might be vars in stck *)
let ifNeedBoxing = ref [];; 
let readMightNeedBoxing = ref [];;  (* a list of pairs [("r" ,ind) , ... ] contains all get-occurences of testedVar that might need boxing *)
let writeMightNeedBoxing = ref [];;  (* a list of pairs [("w" ,ind) , ... ] contains all set-occurences of testedVar that might need boxing *)

(*isOnStack: indicates if we are in the top level of the recursion call == vars will be copied to lexical address from stack frame
  expr = the body of tested lambda 
  testedVar = name of a var that we are asking if needs boxing aka. "x" *)
let rec collectAllReadsAndWrites isOnStack expr testedVar = match expr with
| Var'(VarParam(x, _)) when testedVar = x -> readMightNeedBoxing := ("r", 0) :: !readMightNeedBoxing
| Var'(VarBound(x, _, _)) when testedVar = x -> readMightNeedBoxing := ("r", !ribNumber) :: !readMightNeedBoxing
| If'(test,dit,dif) -> 
  collectAllReadsAndWrites isOnStack test testedVar; 
  collectAllReadsAndWrites isOnStack dit testedVar; 
  collectAllReadsAndWrites isOnStack dif testedVar |> ignore
| Seq'(exprList) -> 
  List.map (fun e -> collectAllReadsAndWrites isOnStack e testedVar) exprList |> ignore
| Set'(Var'(VarParam(x, _)), expr2) when testedVar = x -> 
  writeMightNeedBoxing := ("w", 0) :: !writeMightNeedBoxing; collectAllReadsAndWrites isOnStack expr2 testedVar |> ignore
| Set'(Var'(VarBound(x, _, _)), expr2) when testedVar = x -> 
  writeMightNeedBoxing := ("w", !ribNumber) :: !writeMightNeedBoxing; collectAllReadsAndWrites isOnStack expr2 testedVar |> ignore
| Set'(expr1, expr2) -> collectAllReadsAndWrites isOnStack expr2 testedVar |> ignore 
| BoxSet'(VarParam(x, _), expr2) when testedVar = x -> collectAllReadsAndWrites isOnStack expr2 testedVar |> ignore
| BoxSet'(VarBound(x, _, _), expr2) when testedVar = x -> collectAllReadsAndWrites isOnStack expr2 testedVar |> ignore
| BoxSet'(expr1, expr2) -> collectAllReadsAndWrites isOnStack expr2 testedVar |> ignore
| Or'(exprList) -> 
  List.map (fun e -> collectAllReadsAndWrites isOnStack e testedVar) exprList |> ignore
| LambdaSimple'(stringList, body) when not (List.mem testedVar stringList) -> 
  if isOnStack = 0 
  then handleCopyingFromStack body testedVar
  else collectAllReadsAndWrites isOnStack body testedVar 
| LambdaOpt' (stringList, string, body) when not (List.mem testedVar (stringList @ [string]))->  
  if isOnStack = 0 
  then handleCopyingFromStack body testedVar
  else collectAllReadsAndWrites isOnStack body testedVar 
| Applic'(expr, exprList) -> 
  collectAllReadsAndWrites isOnStack expr testedVar; List.map (fun e -> collectAllReadsAndWrites isOnStack e testedVar) exprList |> ignore
| ApplicTP'(expr, exprList) -> 
  collectAllReadsAndWrites isOnStack expr testedVar; List.map (fun e -> collectAllReadsAndWrites isOnStack e testedVar) exprList |> ignore
| _ -> () (*not intresting, const getBox etc..*)

and handleCopyingFromStack body testedVar =
  ribNumber := !ribNumber + 1;      (* increase number of ribs because it is a new copy of the variable from stack *)
  collectAllReadsAndWrites 1 body testedVar;;  

(* gets !writeMightNeedBoxing !readMightNeedBoxing returns void. changes varsToBox to be [] or [true..];; *)
let rec verifyIfNeedToBox r w = match r, w with
  | [] , [] -> ()
  | [] , x when x != [] -> ()
  | x , [] when x != [] -> ()
  | ("r" , ind1) :: rTl , ("w", ind2) :: wTl when ind1 != ind2 -> ifNeedBoxing := true :: !ifNeedBoxing
  | rHd :: rTl , wHd :: wTl -> verifyIfNeedToBox rTl w ; verifyIfNeedToBox r wTl
  | _ -> ();;

let cleanGlobalAndContinue body = 
  ifNeedBoxing := [];
  writeMightNeedBoxing := [];  
  readMightNeedBoxing := []; 
  body;;

let rec rewriteExp body testedVar = match body with
  | Var'(VarParam(x, i)) when testedVar = x -> BoxGet'(VarParam(x, i))
  | Var'(VarBound(x, i, j)) when testedVar = x ->  BoxGet'(VarBound(x, i, j))
  | If'(test,dit,dif) -> If'(rewriteExp test testedVar, rewriteExp dit testedVar, rewriteExp dif testedVar)
  | Seq'(exprList) -> Seq'(List.map (fun e -> rewriteExp e testedVar) exprList)
  | Set'(Var'(VarParam(x, i)), expr2) when testedVar = x -> BoxSet'(VarParam(x, i), rewriteExp expr2 testedVar)
  | Set'(Var'(VarBound(x, i, j)),expr2) when testedVar = x -> BoxSet'(VarBound(x, i, j) , rewriteExp expr2 testedVar)
  | Set'(expr1,expr2) -> Set'(expr1 , rewriteExp expr2 testedVar) 
  | BoxSet'(expr1, expr2) -> BoxSet'(expr1, rewriteExp expr2 testedVar)
  | Or'(exprList) -> Or'(List.map (fun e -> rewriteExp e testedVar) exprList)
  | LambdaSimple'(stringList, expr) when not (List.mem testedVar stringList) -> LambdaSimple'(stringList, rewriteExp expr testedVar)
  | LambdaOpt' (stringList, string, expr) when not (List.mem testedVar (stringList @ [string]))-> LambdaOpt' (stringList, string, rewriteExp expr testedVar)
  | Applic'(expr, exprList) ->  Applic'(rewriteExp expr testedVar, List.map (fun e -> rewriteExp e testedVar) exprList)
  | ApplicTP'(expr, exprList) ->  ApplicTP'(rewriteExp expr testedVar, List.map (fun e -> rewriteExp e testedVar) exprList)
  | _ -> body;;

let checkSeqAndRewrite body param minor = 
  let newSet = Set'(Var'(VarParam(param, minor)), Box'(VarParam(param, minor))) in
  match body with
    | Seq'((Set'(Var'(VarParam(x, i)), Box'(VarParam(y,j)))) :: rest) when x=y && i=j -> 
          let oldSet = Set'(Var'(VarParam(x, i)), Box'(VarParam(y,j))) in
          Seq'(newSet :: oldSet :: (List.map (fun e -> rewriteExp e param) rest))
    | Seq'(oldBody) -> Seq'(newSet :: [Seq'((List.map (fun e -> rewriteExp e param) oldBody))])
    | _ -> Seq'(newSet :: [rewriteExp body param])

let boxVar body param minor =
  collectAllReadsAndWrites 0 body param;
  verifyIfNeedToBox !readMightNeedBoxing !writeMightNeedBoxing;
  if (List.length !ifNeedBoxing != 0)
  then cleanGlobalAndContinue (checkSeqAndRewrite body param minor)
  else cleanGlobalAndContinue body;;

let rec task3 exprtag = match exprtag with
  | If'(test,dit,dif) -> If'(task3 test, task3 dit, task3 dif)
  | Seq'(exprList) -> Seq'(List.map (fun e -> task3 e) exprList)
  | Set'(expr1,expr2) -> Set'(expr1, task3 expr2)
  | BoxSet'(expr1, expr2) -> BoxSet'(expr1, task3 expr2)
  | Def'(expr1, expr2) -> Def'(expr1, task3 expr2)
  | Or'(exprList) -> Or'(List.map (fun e -> task3 e) exprList)
  | LambdaSimple'(stringList, body)  -> LambdaSimple'(stringList, boxAllVars stringList body)
  | LambdaOpt' (stringList, string, body) -> LambdaOpt' (stringList, string, boxAllVars (stringList @ [string]) body)
  | Applic'(expr, exprList) ->  Applic'(task3 expr, List.map (fun e -> task3 e) exprList)
  | ApplicTP'(expr, exprList) ->  ApplicTP'(task3 expr, List.map (fun e -> task3 e) exprList)
  | _ -> exprtag   (*not intresting, const setBox etc..*)

and boxAllVars stringList body =
  let newBody = goOverAllParams ((List.length stringList)-1) stringList body in
  task3 newBody

and goOverAllParams i stringList body =
  if i >= 0
  then let newBody = boxVar body (List.nth stringList i) i in 
  goOverAllParams (i-1) stringList newBody
  else body;;

let annotate_lexical_addresses e = convertToExprTag [] e;;

let annotate_tail_calls e = convertToApplicTP false e;;

let box_set e = task3 e;;

let run_semantics expr =
 box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

(********************************* our code ends here *********************************)

end;; (* struct Semantics *)