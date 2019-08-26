#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

(******************************** compare functions ********************************)
let checkIfConstsEqual const1 const2 = expr'_eq (Const'(const1)) (Const'(const2));;
let checkIfStringsEqual str1 str2 = String.equal str1 str2;;
let rec checkIfSExists compareFunc x withoutDup = match withoutDup with
  | [] -> false
  | hd :: tl when compareFunc x hd -> true
  | hd :: tl -> checkIfSExists compareFunc x tl;;  

let addOnlyIfNotExists x withoutDup compareFunc = 
  let isEqual = checkIfSExists compareFunc x withoutDup in
  if (isEqual) 
  then withoutDup
  else withoutDup @ [x];;

(**************************** make_fvars_tbl starts here ****************************)
let rec collectFreeVars exprTag freeVarsTable = match exprTag with
  | Var'(VarFree(v)) -> [v] 
  | Box'(VarFree(v)) -> [v] 
  | BoxGet'(VarFree v) -> [v] 
  | BoxSet'(VarFree v, expr) -> [v] @ (collectFreeVars expr freeVarsTable)
  | BoxSet'(v, expr) -> (collectFreeVars expr freeVarsTable)
  | If'(test, dit, dif) -> (collectFreeVars test freeVarsTable) @ (collectFreeVars dit freeVarsTable) @ (collectFreeVars dif freeVarsTable)
  | Seq'(exprList) -> List.fold_right (fun curr acc -> (collectFreeVars curr acc) @ acc) exprList []
  | Set'(expr1, expr2) -> (collectFreeVars expr1 freeVarsTable) @ (collectFreeVars expr2 freeVarsTable)
  | Def'(expr1, expr2) -> (collectFreeVars expr1 freeVarsTable) @ (collectFreeVars expr2 freeVarsTable)
  | Or'(exprList) -> List.fold_right (fun curr acc -> (collectFreeVars curr acc) @ acc) exprList []
  | LambdaSimple'(stringList, expr) -> collectFreeVars expr freeVarsTable
  | LambdaOpt'(stringList, string, expr) -> collectFreeVars expr freeVarsTable
  | Applic'(expr, exprList) -> (collectFreeVars expr freeVarsTable) @
                               (List.fold_right (fun curr acc -> (collectFreeVars curr acc) @ acc) exprList [])
  | ApplicTP'(expr, exprList) -> (collectFreeVars expr freeVarsTable) @
                                (List.fold_right (fun curr acc -> (collectFreeVars curr acc) @ acc) exprList [])
  | _ -> [] ;; (*Const', VarParam, VarBound *)  
  
(* goes over given freeVarsTable and returns a list of tupples (name, offset) for each free var in the table*)
let rec addOffAndAddr freeVarsTable offset = match freeVarsTable with 
  | [] ->  []
  | str :: rest -> (str, offset) :: (addOffAndAddr rest (offset+1))

(* called by make_fvars_tbl, returns the fvar_tbl *)
let createFreeVarsTable asts = 
  let withDup =  List.fold_right (fun curr acc -> acc @ (collectFreeVars curr acc)) asts [] in
  let withoutDup = List.fold_right (fun curr acc ->  addOnlyIfNotExists curr acc checkIfStringsEqual) (List.rev withDup) [] in 
  let defaultTupless = addOffAndAddr withoutDup 0 in defaultTupless;;

(**************************** make_const_tbl starts here *************************)
let rec collectConsts exprTag constantsTable = match exprTag with
  | Const'(const) -> [const]
  | BoxSet'(var, expr) -> (collectConsts expr constantsTable)
  | If'(test, dit, dif) -> (collectConsts test constantsTable) @ (collectConsts dit constantsTable) @ (collectConsts dif constantsTable) 
  | Seq'(exprList) -> List.fold_right (fun curr acc -> (collectConsts curr acc) @ acc) exprList []
  | Set'(var, expr) -> (collectConsts expr constantsTable)
  | Def'(var, expr) -> (collectConsts expr constantsTable)
  | Or'(exprList) -> List.fold_right (fun curr acc -> (collectConsts curr acc) @ acc) exprList []
  | LambdaSimple'(stringList, expr) -> (collectConsts expr constantsTable)
  | LambdaOpt'(stringList,string,expr) -> (collectConsts expr constantsTable)
  | Applic'(expr, exprList) -> (collectConsts expr constantsTable) @
                               (List.fold_right (fun curr acc -> (collectConsts curr acc) @ acc) exprList [])
  | ApplicTP'(expr, exprList) -> (collectConsts expr constantsTable) @
                               (List.fold_right (fun curr acc -> (collectConsts curr acc) @ acc) exprList [])
  | _ -> [] (*var', box', boxGet'*)
  
(* gets the const_tbl and add to it the sub-sexprs of the complex consts (symbol, pair and vector ) *)
let rec expandConsts = function
  | Sexpr(Symbol(x)) -> Sexpr(String(x)) :: [Sexpr(Symbol(x))]
  | Sexpr(Pair(car, cdr)) -> (expandConsts (Sexpr(car))) @ (expandConsts (Sexpr(cdr))) @ [Sexpr(Pair(car, cdr))]
  | Sexpr(Vector(x)) -> (List.fold_right (fun curr acc ->  (expandConsts (Sexpr(curr))) @ acc) x [])  @ [Sexpr(Vector(x))]
  | Sexpr(Nil) -> [] 
  | Sexpr(x) -> [Sexpr(x)]
  | Void -> [];;  

(* goes over given constantsTable and returns a list of tupples (name, offset, lable) for each const in the table
   complex sexprs are given a dummy lable *)
let rec addSimpleOffAndAddr constantsTable offset = match constantsTable with 
  | Void :: tl-> (Void , (offset, "MAKE_VOID")) :: addSimpleOffAndAddr tl (offset+1)
  | Sexpr(Nil) :: tl -> (Sexpr(Nil) , (offset, "MAKE_NIL")) :: addSimpleOffAndAddr tl (offset+1)
  | Sexpr(Bool(false))  :: tl -> (Sexpr(Bool(false)) ,(offset, "MAKE_BOOL(0)")) :: addSimpleOffAndAddr tl (offset+2)
  | Sexpr(Bool(true)) :: tl -> (Sexpr(Bool(true)) ,(offset, "MAKE_BOOL(1)")) :: addSimpleOffAndAddr tl (offset+2)
  | Sexpr(Number(Int(x))) :: tl -> (Sexpr(Number(Int(x))) , (offset, Printf.sprintf ("MAKE_LITERAL_INT(%d) ; offset %d") x offset)) :: addSimpleOffAndAddr tl (offset+9)
  | Sexpr(Number(Float(x))) :: tl -> (Sexpr(Number(Float(x))) , (offset, Printf.sprintf ("MAKE_LITERAL_FLOAT(%f) ; offset %d") x offset)) :: addSimpleOffAndAddr tl (offset+9)
  | Sexpr(Char(x)) :: tl -> (Sexpr(Char(x)), (offset, Printf.sprintf ("MAKE_LITERAL_CHAR(%d) ; offset %d")  (Char.code x) offset)) :: addSimpleOffAndAddr tl (offset+2)
  | Sexpr(String(x)) :: tl -> (Sexpr(String(x)), (offset, Printf.sprintf ("MAKE_LITERAL_STRING  %s ; string: %s offset %d, ")
  (String.concat "," (List.map (fun c -> (string_of_int (int_of_char c))) (string_to_list x))) (String.escaped x) offset)) :: addSimpleOffAndAddr tl (offset+9+ (String.length x))
  | Sexpr(Symbol(x)) :: tl -> (Sexpr(Symbol(x)), (offset, "DUMMY")) :: addSimpleOffAndAddr tl (offset+9)
  | Sexpr(Pair(car,cdr)) :: tl-> (Sexpr(Pair(car,cdr)), (offset, "DUMMY")) :: addSimpleOffAndAddr tl (offset+17)
  | Sexpr(Vector(x)) :: tl -> (Sexpr(Vector(x)), (offset, "DUMMY")) :: addSimpleOffAndAddr tl (offset+9+(8*(List.length x)))
  | [] -> [];;

(* returns the offset/address of a sub-sexpr *)
let rec findAddress constantsTable vartofind = match constantsTable with 
  | (Sexpr(x) , (offset, _ )) :: tl when sexpr_eq x vartofind -> offset
  | (x , (offset, _ )) :: tl -> findAddress tl vartofind
  | [] -> 0;;

(* adds the real lables to all complex sexprs *)
let rec addComplexOffAndAddr table origTable = match table with
  | (Sexpr(Symbol(x)), (offset, "DUMMY")) :: tl -> 
  (Sexpr(Symbol(x)), (offset, Printf.sprintf ("MAKE_LITERAL_SYMBOL(const_tbl+%d) ; offset %d") (findAddress origTable (String(x))) offset)) 
  :: addComplexOffAndAddr tl origTable
  | (Sexpr(Pair(car,cdr)), (offset, "DUMMY")) :: tl-> 
  (Sexpr(Pair(car,cdr)), (offset, Printf.sprintf ("MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d) ; offset %d")
     (findAddress origTable (car)) (findAddress origTable (cdr)) offset))
  :: addComplexOffAndAddr tl origTable
  | (Sexpr(Vector(x)), (offset, "DUMMY")) :: tl -> 
  (Sexpr(Vector(x)), (offset, Printf.sprintf ("MAKE_LITERAL_VECTOR  %s ; offset %d")
  (String.concat " , " (List.map (fun e -> "const_tbl+" ^ (string_of_int (findAddress origTable e))) x)) offset)) :: addComplexOffAndAddr tl origTable
  | x :: tl -> x :: addComplexOffAndAddr tl origTable
  | [] -> table;;

(* called by make_consts_tbl, returns the const_tbl *)  
let createConstsTable asts = 
  let initList =  List.fold_right (fun curr acc -> acc @ (collectConsts curr acc)) asts [] in
  let withDup = List.fold_right (fun curr acc ->  (expandConsts curr) @ acc) initList [] in
  let withoutDup = List.fold_right (fun curr acc ->  addOnlyIfNotExists curr acc checkIfConstsEqual) (List.rev withDup) [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))] in 
  let firstRound = addSimpleOffAndAddr withoutDup 0 in 
  let secondRound = addComplexOffAndAddr firstRound firstRound in secondRound;;

(**************************** make_const_tbl ends here *************************)

(**************************** generate starts here *************************)
let labelsIndex = ref (-1);;
let labelGen str =  labelsIndex := !labelsIndex + 1; str ^ (string_of_int !labelsIndex);;

let rec generateExpr const_tbl fvars_tbl e currEnvSize = match e with 
  | Const'(v) -> getConst const_tbl v
  | Var'(VarFree(v)) -> getFree fvars_tbl v
  | Var'(VarParam(_, minor)) -> getVarParam minor
  | Var'(VarBound(_, major, minor)) -> getVarBound major minor
  | Box'(VarParam(var, minor)) -> 
        "\t;Box\n" ^ (generateExpr const_tbl fvars_tbl (Var'(VarParam(var, minor))) currEnvSize) ^ genBox ^ "\t;End of Box\n"
  | BoxGet'(v) -> 
        "\t;BoxGet\n" ^ (generateExpr const_tbl fvars_tbl (Var'(v)) currEnvSize) ^ Printf.sprintf "\tmov rax, qword[rax]\n\t;Enf of BoxGet\n"
  | BoxSet'(v, expr) -> 
        "\t;BoxSet\n" ^ genBoxSet (generateExpr const_tbl fvars_tbl expr currEnvSize) ( generateExpr const_tbl fvars_tbl (Var'(v)) currEnvSize)
  | If'(test, dit, dif) -> 
        "\t;If\n" ^ (genIf (labelGen "Lelse") (labelGen "Lexit") const_tbl fvars_tbl test dit dif currEnvSize) ^ "\t;End of If\n"
  | Seq'(exprList) -> 
        "\t;Seq starts here\n" ^ (List.fold_right (fun curr acc -> (generateExpr const_tbl fvars_tbl curr currEnvSize) ^ acc) exprList "") ^ "\t;End of Seq\n"
  | Set'(Var'(VarParam(_, minor)), expr) -> 
        "\t;setVarParam\n" ^ generateExpr const_tbl fvars_tbl expr currEnvSize ^ (setVarParam minor)
  | Set'(Var'(VarBound(_,major,minor)),expr) -> 
        "\t;setVarBound\n" ^ generateExpr const_tbl fvars_tbl expr currEnvSize ^ (setVarBound major minor)
  | Set'(Var'(VarFree(v)),expr) -> 
        "\t;setVarFree\n" ^ generateExpr const_tbl fvars_tbl expr currEnvSize ^ (setVarFree fvars_tbl v)
  | Def'(Var'(VarFree(v)), expr) -> 
        "\t;Define\n" ^ generateExpr const_tbl fvars_tbl expr currEnvSize ^ (setVarFree fvars_tbl v) ^ "\t;End of Define\n"
  | Or'(exprList) -> 
        "\t;Or\n" ^ genOr (labelGen "Lexit") exprList const_tbl fvars_tbl currEnvSize ^  "\t;End of Or\n"
  | LambdaSimple'(stringList, expr) -> 
        let newSize = (currEnvSize+1) in "\t;LamSimple\n" ^ 
        genLambda newSize (generateExpr const_tbl fvars_tbl expr newSize) (List.length stringList) false ^ "\t;End LamSimple\n"
  | LambdaOpt'(stringList, string, expr) -> 
        let newSize = (currEnvSize+1) in "\t;LamOpt\n" ^ 
        genLambda newSize (generateExpr const_tbl fvars_tbl expr newSize) ((List.length stringList) +1) true ^ "\t;End LamOpt\n"
  | Applic'(proc, exprList) -> 
        "\t;Applic\n" ^ genApplic proc exprList const_tbl fvars_tbl currEnvSize false ^ "\t;End of Applic\n"
  | ApplicTP'(proc, exprList) -> 
        "\t;ApplicTP\n" ^ genApplic proc exprList const_tbl fvars_tbl currEnvSize true ^ "\t;End of ApplicTP\n"
  | _-> ""

and genApplic proc exprList const_tbl fvars_tbl currEnvSize isTP = 
  let pushMagic = (generateExpr const_tbl fvars_tbl (Const'(Sexpr(Nil))) currEnvSize) ^ "\tpush rax\n" in
  let pushArgs = String.concat " " (List.rev_map (fun e -> (generateExpr const_tbl fvars_tbl e currEnvSize) ^ "\tpush rax\n") exprList) in
  let pushN = (Printf.sprintf("\tpush %d\n") (List.length exprList)) in
  let proc = generateExpr const_tbl fvars_tbl proc currEnvSize in
  let verifyClosure = (Printf.sprintf
  "push rbx
  mov bl, byte [rax]
  cmp bl, T_CLOSURE
  pop rbx
  jne exitWithError
  ") in
  let pushEnv = "\tpush qword[rax+1]\n" in
  let continue = 
  if isTP
  then (Printf.sprintf
 "push qword[rbp+8*1]  ; old ret addr
  push qword[rbp+8*0]  ; old rbp
  ; calc farme size in order to fix rsp
  mov r14,PARAM_COUNT
  add r14,5
  shl r14,3
  SHIFT_FRAME %d, 5
  ; fix rsp
  add rsp,r14
  pop rbp
  jmp [rax+9]
  ") ((List.length exprList) + 5)
  else 
  (Printf.sprintf
  "call [rax+9]
   add rsp, 8*1
   pop rbx ;pop n
   inc rbx
   shl rbx, 3 ; rbx=rbx*8
   add rsp, rbx ;pop args
  ") in
  pushMagic ^ pushArgs ^ pushN ^ proc ^ verifyClosure ^ pushEnv ^  continue 
  
and genLambda extSize body argsCount isOpt =  
  let copy_pointers = labelGen "copy_pointers" in
  let copy_pararms_loop = labelGen "copy_pararms_loop" in
  let copy_pararms = labelGen "copy_pararms" in
  let dummy = labelGen "dummy" in
  let codeL = labelGen "Lcode" in
  let contL = labelGen "Lcont" in
  let codeLjump = labelGen "codeLjump" in
  let fixStack = if isOpt
                 then genLambdaOtp argsCount codeLjump
                 else "" in
  Printf.sprintf "
    push rcx                ; save old value of rcx
    push rbx                ; save old value of rbx
    push r9
    push r8
    MALLOC rbx, %d          ; rbx points to extended lex env |prevEnv+1|*8
    mov r8, qword[rbp+8*2]  ; r8 points to the current lex env
    mov rcx, %d
    cmp rcx, 0                     
    je %s
    ;;; not first lambda, need to extand a real env.

    ;; start copy pinters extandEnv[i+1] = prevEnv[i]
    ;; rcx = |prevEnv|
    ;; we don't need the junk in the pevEnv[n-1] because it is the dummy
  %s: 
    dec rcx                        ; rcx = i-1
    mov r9, qword[r8+8*rcx]        ; r9 = r8[i] (pointer to some minor in the lex env, n to 0)
    inc rcx                        ; rcx = i 
    mov qword[rbx+8*rcx], r9       ; rbx[i+1] = r8[i] 
    loop %s             ; at the end, rbx = exnEnv without ExEnv[0]    

  %s: 
    ;; allocate memory to |ExEnv[0]| = |n*8|
    mov rcx, PARAM_COUNT           ; rcx = n
    
    ;; adding space for magic
    inc rcx

    imul rcx, rcx, WORD_SIZE
    MALLOC r9, rcx                 ; r9 pointer to memory |n*8|
    mov qword[rbx+8*0], r9         ; ExEnv[0] = rbx[0] = |n*8|
    ;; start copy n params from stack
    mov rcx, PARAM_COUNT           ; rcx = n

    ;; adding magic to last place in ExEnv[0]
    ;inc rcx         ; rcx = n+1
    mov qword[r9+8*rcx], const_tbl+1         ; r9[n] = nil
    ;dec rcx

    cmp rcx, 0                     ; check that n != 0 if not, do not copy params and create closure
    je %s
  %s:    
    dec rcx                         ; rcx = n-1
    mov r8 ,qword[rbp+8*(4+rcx)]    ; r8 = Ai (n to 0)
    mov qword[r9+8*rcx], r8         ; r9[i] = Ai
    inc rcx                         ; rcx = n
    loop %s

  %s:
    MAKE_CLOSURE(rax, rbx, %s)
    pop r8
    pop r9
    pop rbx
    pop rcx
    jmp %s
  %s: 
    push rbp
    mov rbp, rsp
    %s 
  %s:   
    %s  
    leave
    ret
  %s:
  " (extSize*8) (extSize-1) dummy copy_pointers copy_pointers copy_pararms dummy copy_pararms_loop copy_pararms_loop dummy codeL contL codeL fixStack codeLjump  body contL               

and genLambdaOtp argsCount codeLjump = 
  let fixStack = labelGen "fix_stack" in
  let extandList = labelGen "extandList" in
  let vardiac = labelGen "vardiac" in
    Printf.sprintf "  
    ;; starting speical code for lambda optional
    ;; because we are using magic, need to consider the following cases:
    ;; let n = number of params passed to applic
    ;; let argsCount = number of expected params
    ;; 1) if n < argsCount  ->  nothing to do, magic will do anyting for us, exit
    ;; 2) if n = argsCount  -> need to wrap otional param with list and exit
    ;; 3) if n > argsCount  -> need to wrap and fix stack
    
    mov r13, PARAM_COUNT  
    mov rcx, PARAM_COUNT                ; check if argsCount = n
    cmp rcx, %d                         
    jl %s                               ; case 1)

    ; step 1: create (An, Nil) and replace An with it
    mov rcx, PARAM_COUNT                ; rcx = n
    dec rcx                             ; rcx = n-1    
    ; make pair (An, Nil)
    mov r11,  qword[rbp+8*(4+rcx)]      ; r11 = An
    mov r12, const_tbl+1                ; r12 = Nil
    MAKE_PAIR(rbx, r11, r12)            ; rbx = pointer to (An. Nil)
    mov r10, rbx                        ; r10 = pointer to (An, Nil)
    mov qword[rbp+8*(4+rcx)], r10       ; An points to (An, Nil)
    ; check id it is cas#2 and exit / continue
    inc rcx                             ; rcx = n
    cmp rcx, %d                         ; check if argsCount = n
    je %s                               ; case 2)

    ; we are in case 3) 
    ; step 2: extand the list to contain all optional params
    ; r10 points to  (An, Nil)
    ; rcx is the loop's counter = offset
    ; rdx is for taking the params from stack

    ;inc rcx         ; rcx = n
    mov rdx, rcx                        ; rdx = rcx = n
    dec rdx                             ; rdx = n-1
    sub rcx, %d                         ; rcx = offset
  %s: 
    dec rdx                             ; rdx = n -1
    mov r11,  qword[rbp+8*(4+rdx)]      ; r11 = Ai from stack
    MAKE_PAIR(rbx, r11, r10)            ; rbx = pointer to new pair (Ai, oldPair)
    mov r10, rbx                        ; r10 = rbx = pointer to new pair (Ai, oldPair)
    loop %s

    mov rbx, PARAM_COUNT                ; rbx = n
    dec rbx                             ; rbx = n -1                
    mov qword[rbp+8*(4+rbx)], r10       ; An points to optional list

    ;; step 3: move up all the params on stack sent to applic
    mov rcx, %d                         ; rcx = argsCount 
    ; specianl check for vardiac 
    cmp rcx, 1                          
    je %s
    dec rcx                             ; rcx = argsCount -1       
  %s:
    dec rcx  
    dec rbx           
    mov r11, qword[rbp+8*(4+rcx)]
    mov qword[rbp+8*(4+rbx)], r11
    inc rcx
    loop %s
    ; step 4: move up all other stuff on stack - n, env, ret etc.
  %s:
    ; update n to be the |argsCount| and place it in the updated position on stack
    dec rbx
    mov qword[rbp+8*(4+rbx)], %d 
    dec rbx
    ; move up the lex env
    mov r11, qword[rbp+8*2]
    mov qword[rbp+8*(4+rbx)], r11 
    dec rbx
    ; move up the ret address
    mov r11, qword[rbp+8*1]
    mov qword[rbp+8*(4+rbx)], r11   
    dec rbx 
    ;;  move up the old rbp 
    mov r11, qword[rbp+8*0]
    mov qword[rbp+8*(4+rbx)], r11
    ;mov qword[rbp+8*3], r11
    mov r11, r13                    ; r11 = n
    sub r11, %d                     ; r11 = offset
    ; fix rsp
    shl r11, 3
    add rsp, r11
    ; fix rbp
    mov rbp,rsp
    jmp %s
  "argsCount codeLjump argsCount codeLjump argsCount extandList extandList argsCount vardiac fixStack fixStack vardiac argsCount argsCount codeLjump
  
and getConst const_tbl v =
  let const_row = List.find (fun (const, (_, _)) -> checkIfConstsEqual const v) const_tbl in
  let offset = (fun (_, (off, _)) -> off) const_row in Printf.sprintf "\tmov rax, const_tbl+%d\n" offset

and getFreeOffset fvars_tbl var = List.find (fun (currVar, offset) -> String.equal var currVar) fvars_tbl  
and getFree fvars_tbl var =
  let (var, offset) = getFreeOffset fvars_tbl var in
  Printf.sprintf "\tmov rax, FVAR(%d)  ;getFreeVar\n" offset

and setVarFree fvars_tbl v = 
  let (v, offset) = getFreeOffset fvars_tbl v in  
  Printf.sprintf "\tmov FVAR(%d), rax\n\tmov rax, SOB_VOID_ADDRESS  \n\t;set! returns void\n" offset

and getVarParam minor = Printf.sprintf "\tmov rax, qword[rbp+8*(4+%d)]  ;getVarParam\n" minor
and setVarParam minor = Printf.sprintf "\tmov qword[rbp+8*(4+%d)], rax\n\tmov rax, SOB_VOID_ADDRESS  \n\t;set! returns void\n" minor 
and getVarBound major minor = Printf.sprintf "\t;getVarBound\n\tmov rax, qword[rbp+8*2] ; get lex env \n\tmov rax, qword[rax+8*%d] ; get major\n\tmov rax, qword[rax+8*%d] ; get minor\n\t;end of getVarBound\n" major minor
and setVarBound major minor = Printf.sprintf "\tmov rbx, qword[rbp+8*2] ; get lex env\n\tmov rbx, qword[rbx+8*%d] ; get major\n\tmov qword [rbx+8*%d], rax ;get minor\n\tmov rax, SOB_VOID_ADDRESS \n\t;set! retuns void\n" major minor
and genOr label exprList const_tbl fvars_tbl currEnvSize = 
  let revList = List.rev exprList in
  let firsts = List.tl revList in
  let lastExpr = List.hd revList in
  let firsts = List.rev firsts in 
  (List.fold_right (fun curr acc -> (generateExpr const_tbl fvars_tbl curr currEnvSize) ^ 
                                    (Printf.sprintf "\tcmp word[rax], SOB_FALSE\n\tjne %s\n") label ^ 
                                    acc) 
                                    firsts 
                                    "") ^ (generateExpr const_tbl fvars_tbl lastExpr currEnvSize) ^  (Printf.sprintf "%s:\n") label

and genIf elseL exitL const_tbl fvars_tbl test dit dif  currEnvSize = 
  "\t;test:\n" ^ (generateExpr const_tbl fvars_tbl test currEnvSize) ^ (Printf.sprintf "\tcmp word[rax], SOB_FALSE\n\tje %s\n" elseL)  ^ 
  "\t;then:\n" ^ (generateExpr const_tbl fvars_tbl dit currEnvSize) ^ (Printf.sprintf "\tjmp %s\n%s:\n" exitL elseL) ^ 
  "\t;else:\n" ^ (generateExpr const_tbl fvars_tbl dif currEnvSize) ^ (Printf.sprintf "\t%s:\n" exitL) 

and genBoxSet expr var = Printf.sprintf "%s\tpush rax\n%s\tpop qword[rax]\n\tmov rax, SOB_VOID_ADDRESS\n\t;end of BoxSet\n" expr var
and genBox = 
  (Printf.sprintf
        "\tpush rax
        \tMALLOC rax, 8    
        \tpop qword[rax]\n
        ") ;;

(**************************** generate ends here *************************)

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = createConstsTable asts;;
  let make_fvars_tbl asts = createFreeVarsTable asts ;;
  let generate consts fvars e = generateExpr consts fvars e 0;;
end;;  
