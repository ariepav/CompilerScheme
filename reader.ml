
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> 
  if ((List.length l1) = (List.length l2))
  then List.for_all2 sexpr_eq l1 l2
  else false
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(************************************************* Our Code ****************************************)
let _dot_ = char '.';;
let _lp_ = char '(';;
let _rp_ = char ')';;
let _lb_ = char '[';;
let _rb_ = char ']';;
let _close_all_ = word "...";;
let _open_ = disj _lp_ _lb_;;
let _close_ = disj _rp_ _rb_;;

(*SymbolChar*)
let _symbol_char_ = 
  let _lower_ = pack (range 'A' 'Z') (fun (a) -> lowercase_ascii a) in
  disj_list [(range '0' '9'); (range 'a' 'z'); _lower_ ; (char '!'); (char '$'); (char '^'); (char '*'); (char '-'); (char '_'); (char '='); (char '+'); (char '<');
(char '>'); (char '?'); (char '/'); (char ':')];;

(*Symbol*)
let _symbol_ = pack (plus _symbol_char_) (fun (a) -> Symbol (list_to_string a));;

let _sign_ = 
  let _plus_ = char '+' in
  let _minus_ = char '-' in
  disj (_minus_) (_plus_);;

(*Digit*)
let _digit_ = range '0' '9';;

(*HexDigit*)
let _hex_digit_ = disj_list [_digit_ ; (range 'a' 'f'); (range 'A' 'F')];;

(*Natural*)
let _natural_ = plus _digit_;;

(*Integer*)
let _integer_ = 
  let _int_nt_ = caten (maybe _sign_) _natural_ in
  PC.pack _int_nt_ (fun (s,n) -> match s,n with
  | Some('-'), _ -> ['-']@n
  | _ , _ -> n);;

(*HexNatural*)
let _hex_natural_ = plus _hex_digit_;;

(*HexInteger*)
let _hex_integer_ = 
  let _hex_prefix_ = caten (char '#') (char_ci 'x') in
  let _hex_nt_ = caten (_hex_prefix_) (caten (maybe _sign_) _hex_natural_) in
  pack _hex_nt_ (fun (p , (s, n)) -> match p, (s,n) with
  | _, (Some('-'), _) -> (['-';'0';'x'] @ n)
  | _, (_ , _) -> (['0';'x'] @ n));;

(*Float*)
let _float_ =
  let _fl_nt_ = caten (_integer_) (caten _dot_ _natural_) in
  pack _fl_nt_ (fun (s, (r,n)) -> s@['.']@n);;

(*HexFloat*)
let _hex_float_ = 
  let _hex_fl_nt_ = caten (_hex_integer_) (caten _dot_ _hex_natural_) in
  pack _hex_fl_nt_ (fun (s, (r,n)) -> s@['.']@n);;

(* 4.1 Scientific notation *)  
let _sn_number_ =
  let _nt_ = disj _float_ _integer_ in
  let _nt_ = caten _nt_ (char_ci 'e') in
  let _nt_ = caten _nt_ _integer_ in
  pack _nt_ (fun ((a , e), b) -> a@['e']@b);;

(*Number*)
let _number_ = 
  let _number_nt_ = not_followed_by (disj_list [_hex_float_; _sn_number_ ;_float_; _hex_integer_; _integer_]) (_symbol_) in
  pack _number_nt_ (fun (h) ->
    if ((List.exists (fun e -> e == '.') h )|| (List.exists (fun e -> e == 'e') h)) 
    then Number(Float(float_of_string (list_to_string h)))
    else Number(Int(int_of_string (list_to_string h))));;

(*CharPrefix*)
let _char_prefix_ = caten (char '#') (char '\\');;

(*VisibleSimpleChar*)
let _visible_simple_char_ = range (Char.chr 33)(Char.chr 127) ;;

(*NamedChar*)
let _named_char_ =
  let _nul_=  pack (word_ci "nul") (fun (l) -> Char.chr 0) in
  let _newline_= pack (word_ci "newline") (fun (l) -> Char.chr 10) in
  let _return_=  pack (word_ci "return") (fun (l) -> Char.chr 13) in
  let _tab_=  pack (word_ci "tab") (fun (l) -> Char.chr 9) in
  let _formfeed_=  pack (word_ci "page") (fun (l) -> Char.chr 12) in
  let _space_= pack (word_ci "space") (fun (l) -> Char.chr 32) in
  disj _nul_ (disj _newline_ (disj _return_ (disj _tab_ (disj _formfeed_ _space_)))) 

(*HexChar*)
let _hex_char_ =  
  let _hex_char_nt_ = caten (char_ci 'x') _hex_natural_ in 
  pack _hex_char_nt_ (fun (a,b) -> Char.chr (int_of_string (list_to_string (['0';'x']@b))));;

(*Char*)
let _char_ = pack (caten _char_prefix_ (disj _hex_char_ (disj _named_char_ _visible_simple_char_))) (fun ((a,b), c) -> Char c);; 

(*StringLiteralChar*)
let _string_literal_char_ = disj_list [(range (Char.chr 0) (Char.chr 33)); (range (Char.chr 35) (Char.chr 91)); (range (Char.chr 93) (Char.chr 127))];;

(*StringMetaChar*)
let _string_meta_char_ =    
  let _newline_string_= pack (word_ci "\\n") (fun (l) -> Char.chr 10) in
  let _return_string_=  pack (word_ci "\\r") (fun (l) -> Char.chr 13) in
  let _tab_string_=  pack (word_ci "\\t") (fun (l) -> Char.chr 9) in
  let _formfeed_string_=  pack (word_ci "\\f") (fun (l) -> Char.chr 12) in
  let _backslash_string_= pack (word_ci "\\\\") (fun (l) -> Char.chr 92) in
  let _doublequote_string_= pack (word_ci "\\\"") (fun (l) -> Char.chr 34) in
  disj_list [_newline_string_; _return_string_; _tab_string_;_formfeed_string_;_doublequote_string_;_backslash_string_];;

(*StringHexChar*)
let _string_hex_char_ =
  let _string_hex_char_nt_ = caten (caten (char '\\') (char_ci 'x')) (caten _hex_natural_  (char ';')) in
  pack _string_hex_char_nt_ (fun (a,(b,c)) -> Char.chr (int_of_string (list_to_string (['0';'x']@b))));;

(*StringChar*)
let _string_char_ = disj_list [_string_hex_char_;  _string_meta_char_ ;_string_literal_char_ ];;

(*String *)
let _string_ = 
  let _quote_ = char '"' in
  let _string_nt_ = caten _quote_ (caten (star (diff _string_char_ _quote_)) _quote_) in
  pack _string_nt_ (fun (a,(b,c)) -> String (list_to_string b));;

let _space_ = nt_whitespace;;

(*Sexpr*)
let rec _sexpr_ s = _clean_sexpr_ (disj_list [_nil_; _bool_; _char_; _number_; _string_; _symbol_; _list_; _dotted_list_; _vector_; _quoted_;_qquoted_;_unquoted_; _unquotedspliced_;_balanced_lists_]) s

(*Boolean*)
and  _bool_ s = 
  let _true_ = not_followed_by (caten (char '#') (char_ci 't')) (disj _number_ _symbol_) in
  let _false_ = not_followed_by (caten (char '#') (char_ci 'f')) (disj _number_ _symbol_) in
  let _true_ = pack _true_ (fun (a, b)-> Bool true) in
  let _false_= pack _false_ (fun (a, b) -> Bool false) in
  (disj _true_ _false_) s

(* 3.2 Comments & whitespaces *)
and _space_ s = 
  let _x_ = nt_whitespace in
  let _packed_ = pack _x_ (fun a -> Nil) in
_packed_ s  

and _line_comment_ s =  
  let _x_ = caten (char ';') (star (diff nt_any (char '\n'))) in 
  let _x_ = caten _x_ (char '\n') in
  let _packed_ = pack _x_ (fun ((a ,sl), b) -> Nil) in
_packed_ s   

and _sexpr_comment_ s = 
  let _x_ = caten (char '#') (char ';') in
  let _x_ = caten _x_ _sexpr_ in
  let _packed_ = pack _x_ (fun ((a ,b), sl) -> Nil) in
_packed_ s

and _comments_ s = (disj _line_comment_ _sexpr_comment_) s

and _skips_ s = 
  let _x_ = star (disj _space_ _comments_) in
  let _packed_ = pack _x_ (fun a -> Nil) in
_packed_ s  

(*Nil*)
and _nil_ s = 
  let _nt_ = caten _lp_ (_skips_) in
  let _nt_ = caten _nt_ _rp_ in
  let _packed_ = pack _nt_ (fun ((a, b) ,c) -> Nil) in
_packed_ s  

(* remove all spaces and comments from input *)
and _clean_sexpr_ _nt_ = 
  let _x_ = caten _skips_ _nt_ in
  let _x_ = caten _x_ _skips_ in 
  let _x_ = pack _x_ (fun ((_, e) , _) -> e) in
_x_ 

(* 4.2 Bracket notation for pairs *)
(*List*)
and _create_list_ _lp_ _rp_ s = 
  let _x_ = _lp_ in
  let _x_ = caten _x_ (star _sexpr_) in
  let _x_ = caten _x_ _rp_ in  
  let _packed_ = pack _x_ (fun ((lp ,sl) , rp )-> 
    List.fold_right (fun curr acc -> Pair(curr, acc)) sl Nil) in
_packed_ s

and _list_p_ s = _create_list_ _lp_ _rp_ s
and _list_b_ s = _create_list_ _lb_ _rb_ s
and _list_ s = (disj _list_b_ _list_p_) s

(*DottedList*)
and _create_dotted_list_ _lp_ _rp_ s = 
  let _nt_ = _lp_ in
  let _nt_ = caten _nt_ (plus _sexpr_) in
  let _nt_ = caten _nt_ _dot_ in
  let _nt_ = caten _nt_ _sexpr_ in
  let _nt_ = caten _nt_ _rp_ in
  let _packed_ = pack _nt_ (fun ((((lp , sl) , d) , s), rp) -> 
    List.fold_right (fun curr acc -> Pair(curr, acc)) sl s) in
_packed_ s

and _dotted_list_p_ s = _create_dotted_list_ _lp_ _rp_ s
and _dotted_list_b_ s = _create_dotted_list_ _lb_ _rb_ s
and _dotted_list_ s = (disj _dotted_list_b_ _dotted_list_p_) s

(*Vector*)
and _vector_ s =
  let _nt_ = char '#' in
  let _nt_ = caten _nt_ _lp_ in
  let _nt_ = caten _nt_ (star _sexpr_) in
  let _nt_ = caten _nt_ _rp_  in
  let _packed_ = pack _nt_ (fun (((h , lp) , sl) , rp) -> Vector sl) in
_packed_ s

(*Quoted*)
and _quoted_ s =
  let _nt_ = char '\'' in
  let _nt_ = caten _nt_ _sexpr_ in
  let _packed_ = pack _nt_ (fun (q, s) -> Pair(Symbol("quote"), Pair(s, Nil))) in
_packed_ s

(*QuasiQuoted*)
and _qquoted_ s =
  let _nt_ = char '`' in
  let _nt_ = caten _nt_ _sexpr_ in
  let _packed_ = pack _nt_ (fun (q, s) -> Pair(Symbol("quasiquote"), Pair(s, Nil))) in
_packed_ s

(*Unquoted*)
and _unquoted_ s =
  let _nt_ = char ',' in
  let _nt_ = caten _nt_ _sexpr_ in
  let _packed_ = pack _nt_ (fun (q, s) -> Pair(Symbol("unquote"), Pair(s, Nil))) in
_packed_ s

(*UnquoteAndSpliced*)
and _unquotedspliced_ s =
  let _nt_ = char ',' in
  let _nt_ = caten _nt_ (char '@') in
  let _nt_ = caten _nt_ _sexpr_ in
  let _packed_ = pack _nt_ (fun ((q1, q2), s) -> Pair(Symbol("unquote-splicing"), Pair(s, Nil))) in
_packed_ s

(* 4.3 Automatic balancing of parentheses *)
and _balanced_lists_ s = 
  let _nt_ = _continue_balance_list_ in
  let _nt_ = caten _nt_ _close_all_ in
  let _packed_ = pack _nt_ (fun (sl,b)-> sl ) in
_packed_ s

and _create_continue_balance_list_ _lp_ _rp_ s = 
  let _x_ = caten _lp_ (star (disj (diff _sexpr_ _balanced_lists_) (_continue_balance_list_))) in
  let _x_ = caten _x_ (maybe _rp_) in
  let _packed_ = pack _x_ (fun ((lp, sl) , rp) -> List.fold_right (fun curr acc -> Pair(curr, acc)) sl Nil) in
_packed_ s  

and _create_continue_balance_doted_list_ _lp_ _rp_ s = 
  let _rec_ = disj (diff _sexpr_ _balanced_lists_) (_continue_balance_list_) in
  let _x_ = caten _lp_ (plus _rec_) in
  let _x_ = caten _x_ (char '.')  in
  let _x_ = caten _x_ (diff _rec_ _close_all_) in
  let _x_ = caten _x_ (maybe _rp_) in
  let _packed_ = pack _x_ (fun ((((lp, sl) , d) , s), rp) -> List.fold_right (fun curr acc -> Pair(curr, acc)) sl s) in
_packed_ s  

and _continue_balance_list_ s = _clean_sexpr_ (disj_list [(_create_continue_balance_doted_list_ _lp_ _rp_ );
                                           (_create_continue_balance_doted_list_ _lb_ _rb_ );
                                           (_create_continue_balance_list_ _lp_ _rp_);
                                           (_create_continue_balance_list_ _lb_ _rb_ );
                                           ]) s;;                                           

(*********************************** End of our code ********************************************)
let read_sexpr string = 
   let (e, s) = (_sexpr_ (string_to_list string)) in e;;
let read_sexprs string = 
    let (e, s) = (star _sexpr_) (string_to_list string) in e;;
end;; (* struct Reader *) 