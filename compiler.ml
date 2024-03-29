#use "code-gen.ml";;

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
   "car", "car"; "cdr", "cdr"; "set-car!", "set_car"; "set-cdr!", "set_cdr"; "cons", "cons"; "apply", "apply";
(* you can add yours here *)];;

let make_prologue consts_tbl fvars_tbl =
  let make_primitive_closure (prim, label) =
  try let (_, offset) = List.find (fun (currVar, offset) -> String.equal prim currVar) fvars_tbl in
    "\tMAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")
    mov qword[fvar_tbl+" ^ (string_of_int (offset*8)) ^ "], rax\n" 
  with Not_found -> "" in
  let make_constant (c, (a, s)) = s in
  
"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

section .bss
malloc_pointer:
    resq 1

section .data
const_tbl:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS const_tbl
%define SOB_NIL_ADDRESS const_tbl+1
%define SOB_FALSE_ADDRESS const_tbl+2
%define SOB_TRUE_ADDRESS const_tbl+4

fvar_tbl:
" ^ (String.concat "\n" (List.map (fun _ -> "dq T_UNDEFINED") fvars_tbl)) ^ "

global main
section .text
main:
    ;; set up the heap
    mov rdi, GB(4)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push rbp
    push 0
    push qword SOB_NIL_ADDRESS
    push qword T_UNDEFINED
    push rsp
    mov rbp, rsp

    call code_fragment
    add rsp, 4*8
    pop rbp
    ret

code_fragment:
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
 " ^ String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels) ^  
 "
";;

let epilogue = 
"car:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov al, byte [rsi]
    cmp al, T_PAIR
    jne exitWithError
    mov rax, qword[rsi+1]
    leave
    ret

 cdr:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov al, byte [rsi]
    cmp al, T_PAIR
    jne exitWithError
    mov rax, qword[rsi+9]
    leave
    ret
    
  set_car:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov al, byte [rsi]
    cmp al, T_PAIR
    jne exitWithError
    mov rax, PVAR(1)
    mov qword[rsi+1], rax
    mov rax, SOB_VOID_ADDRESS
    leave
    ret      
    
  set_cdr:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov al, byte [rsi]
    cmp al, T_PAIR
    jne exitWithError
    mov rax, PVAR(1)
    mov qword[rsi+9], rax
    mov rax, SOB_VOID_ADDRESS
    leave
    ret 
  
  cons:
    push rbp
    mov rbp, rsp

    mov rdi, PVAR(1)
    mov rsi, PVAR(0)
    MAKE_PAIR(rax, rsi, rdi)

    leave
    ret     
    
apply:
    push rbp
    mov rbp, rsp

    ; rcx = 0
    mov rcx, 0
    mov r10, qword[rbp+8*0]     ; r10 = old rbp
    ; count the lenght of the optional param (s) and save in reg1 and reg2
    mov rsi, qword[rbp+8*3]           ; rdi = n
    dec rsi                           ; rdi = n-1
    mov rdi, qword[rbp+8*(4+rsi)]     ; rdi = s
.lenght:
    mov al, byte [rdi]
    cmp al, T_PAIR                     ; check if s is pair
    jne .split_list
    inc rcx
    mov rdi, qword[rdi+9]               ; rdi = (cdr s)
    jmp .lenght
    
.split_list:  
    mov rdi, qword[rbp+8*(4+rsi)]           ; rdi = s
    mov r14, rcx                            ; rcx = r14 = length of s
.split_list_loop:
    cmp rcx, 0
    je .copy_params
    mov r8, qword[rdi+1]         ; r8 = car
    imul rcx, rcx, -1
    mov qword[rbp+rcx*WORD_SIZE], r8     ; push car
    imul rcx, rcx, -1
    mov rdi, qword[rdi+9]        ; rdi = (cdr s)
    loop .split_list_loop

    ; inc reg2 and mov qword[rbp+8*(-reg2)], qword[rbp+8*(4+i)] - until reaching qword[rbp+8*(4+0)]
.copy_params:
    mov rcx, qword[rbp+8*3]    
    sub rcx, 2                         ; rcx = n-2
.copy_params_loop:
    cmp rcx, 0
    je .continue
    inc r14
    mov r8, qword[rbp+8*(4+rcx)]         ; r8 = Ai
    imul r14, r14, -1
    mov qword[rbp+r14*WORD_SIZE], r8     ; push Ai to new place
    imul r14, r14, -1
    loop .copy_params_loop

.continue:
    mov rcx, r14                               ; rcx = new n
    inc r14
    imul r14, r14, -1
    mov qword[rbp+r14*WORD_SIZE], rcx           ; push new n to new place
    imul r14, r14, -1

    mov rax, qword[rbp+WORD_SIZE*(4+0)]         ; rac = proc
    ;push rbx                                    ; verify proc is closure
    mov bl, byte [rax]
    cmp bl, T_CLOSURE
    jne exitWithError
    inc r14
    imul r14, r14, -1
    mov rcx, qword[rax+1]
    mov qword[rbp+r14*WORD_SIZE], rcx           ; push proc to new place
    imul r14, r14, -1
    inc r14
    imul r14, r14, -1
    mov rcx, qword[rbp+WORD_SIZE*1]
    mov qword[rbp+r14*WORD_SIZE], rcx           
    imul r14, r14, -1
    ; push old rbp
    inc r14
    imul r14, r14, -1
    mov rcx, qword[rbp+WORD_SIZE*0]
    mov qword[rbp+r14*WORD_SIZE], rcx          
    imul r14, r14, -1

    ; shift and fix frame
    mov rbx, PARAM_COUNT
    mov rcx, PARAM_COUNT
    add rcx, 4
    mov r13,1
    add r14,1
.loop_cmp:
    cmp r13,r14
    je .cont
	  dec rcx
    imul r13, r13, -1
    mov r15, qword[rbp+WORD_SIZE*r13]
    imul r13, r13, -1
    mov qword[rbp+WORD_SIZE*rcx], r15
    inc r13
    jmp .loop_cmp
.cont:
    sub r14,5       ; r14= new n
    sub r14, rbx
    shl r14, 3
    sub rsp,r14
    pop rbp
    jmp qword[rax+9]

    leave
    ret     
    
    nop";; 

exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in
  let code = (file_to_string "stdlib.scm") ^ (file_to_string infile) in 
  let asts = string_to_asts code in 
  let consts_tbl = Code_Gen.make_consts_tbl asts in 
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl in
  let code_fragment = String.concat "\n\n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\n    call write_sob_if_not_void")
                           asts) in
  let provided_primitives = file_to_string "prims.s" in
                   
  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^ "\n ret\n" ^
                    provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;
