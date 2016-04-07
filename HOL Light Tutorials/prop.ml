type term = 
  | Var of string
  | Neg of term
  | Conj of term * term
  | Disj of term * term
  | Imp of term * term;;

type thm = Theorem of term;;

let mk_thm term = Theorem term;;

let dest_thm = function
  | Theorem tm -> tm;;

exception Noparse;;

let (||) parser1 parser2 input =
  try parser1 input
  with Noparse -> parser2 input;;

let (++) parser1 parser2 input =
  let result1, rest1 = parser1 input in
  let result2, rest2 = parser2 rest1 in
  (result1, result2), rest2;;

let nothing input = [], input;;

let rec many prs input =
  try let result, next = prs input in
      let results, rest = many prs next in
      (result :: results), rest
  with Noparse -> [], input;;

let (>>) prs treatment input =
  let result, rest = prs input in
  treatment result, rest;;

let some p = 
  function
    | [] -> raise Noparse
    | (h :: t) -> if p h then (h,t) else raise Noparse;;

let a tok = some (fun item -> item = tok);;

let rec level1 str =
  (
    ((level2 ++ a "->" ++ level2) 
     >> (fun ((t1, _), t2) -> Imp (t1, t2)))
    || level2
  ) str
and level2 str =
  (
    ((level3 ++ a "|" ++ level3) 
     >> (fun ((t1, _), t2) -> Disj (t1, t2)))
    || level3
  ) str
and level3 str =
  (
    ((level4 ++ a "&" ++ level4) 
     >> (fun ((t1, _), t2) -> Conj (t1, t2)))
    || level4
  ) str
and level4 str =
  (
    ((a "~" ++ level4) >> (fun (_, t) -> Neg t))
    || ((a "(" ++ level1 ++ a ")") >> 
	(fun ((_, t), _) -> t))
    || (some (fun _ -> true) >> (fun v -> Var v))
  ) str;;

(level1 $ lex $ explode) "a -> (B -> c & d)";;

let rec lex = 
  function
    | " " :: t -> lex t
    | "-" :: ">" :: t -> "->" :: lex t
    | h :: t -> h :: lex t
    | [] -> [];;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;

let ($) f g x = f (g x);;

let parse_term = fst $ level1 $ lex $ explode;;
let p = parse_term;;

open Format;;

let rec print_term fmt = function
  | Var v -> pp_print_string fmt v
  | Neg t ->
    begin
      pp_print_string fmt "~";
      print_term fmt t
    end
  | Conj (t1, t2) ->
    begin
      pp_print_string fmt "(";
      print_term fmt t1; 
      pp_print_string fmt " & "; 
      print_term fmt t2;
      pp_print_string fmt ")"
    end
  | Disj (t1, t2) -> 
    begin
      pp_print_string fmt "(";
      print_term fmt t1; 
      pp_print_string fmt " | "; 
      print_term fmt t2;
      pp_print_string fmt ")"
    end
  | Imp (t1, t2) -> 
    begin
      pp_print_string fmt "(";
      print_term fmt t1; 
      pp_print_string fmt " -> "; 
      print_term fmt t2;
      pp_print_string fmt ")"
    end;;

let print_theorem fmt th = 
  pp_print_string fmt "|- ";
  print_term fmt (dest_thm th);;

let print_tm = print_term std_formatter;;
let print_thm = print_theorem std_formatter;;

#install_printer print_tm;;
#install_printer print_thm;;

(* Axioms *)
let a1 = mk_thm (parse_term "p -> (q -> p)");;
let a2 = mk_thm (parse_term "(p -> (q -> r)) -> ((p -> q) -> (p -> r))");;
let a3 = mk_thm (parse_term "(~p -> ~q) -> (q -> p)");;

(* Inference Rules *)
let mp pq_th p_th =
  let pq_tm = dest_thm pq_th in
  let p_tm = dest_thm p_th in
  match pq_tm with
    | Imp (p, q) when p = p_tm -> mk_thm q
    | _ -> failwith "mp";;

let rec assoc x =
  function
    | [] -> failwith "assoc"
    | (y, v) :: t ->
      if y = x then v else assoc x t;;

let assocd x list d =
  try assoc x list with Failure _ -> d;;

let subst list =
  let rec sub tm =
    match tm with
      | Var v -> assocd v list tm
      | Neg t -> sub t
      | Conj (t1, t2) -> Conj (sub t1, sub t2)
      | Disj (t1, t2) -> Disj (sub t1, sub t2)
      | Imp (t1, t2) -> Imp (sub t1, sub t2) in
  sub;;

let inst list =
  function Theorem tm -> Theorem (subst list tm);;

mp (inst ["r", p "p"] a2) a1;;


(******************)
(*      Str       *)
(******************)

type str_thm = Str_thm of string;;
let dest_str_thm = function Str_thm str -> str;;

let s0 = Str_thm "a";;
let s1 = Str_thm "b";;

let cat_str th1 th2 =
  let str1, str2 = dest_str_thm th1, dest_str_thm th2 in
  Str_thm (str1 ^ str2 ^ str1);;

let mp_str =
  let split n str =
    let k = String.length str in
    if n <= k then
      String.sub str 0 n, String.sub str n (k - n)
    else
      str, "" in
    fun th1 th2 ->
      let str1, str2 = dest_str_thm th1, dest_str_thm th2 in
      let s1, s2 = split (String.length str2) str1 in
      if s1 = str2 && s2 <> "" then 
	Str_thm s2 
      else failwith ("mp_str: str1 = " ^ str1 ^ "; str2 = " ^ str2);;
  
  
let r1 = cat_str s0 s1;;
let r2 = mp_str r1 s0;;
let r3 = mp_str r2 s1;;

let rec derive str =
  let n = String.length str in
  if n = 0 then failwith "derive: empty string"
  else if str = "a" then s0
  else if str = "b" then s1
  else 
    let head = String.sub str 0 (n - 1) in
    let last = String.sub str (n - 1) 1 in
    let ax = 
      if last = "a" then s0
      else if last = "b" then s1
      else failwith ("derive: bad symbol - " ^ last) in
    mp_str (cat_str ax (derive head)) ax;;


(**********)
(* Lambda *)
(**********)

type term = 
  | Var of string
  | App of term * term
  | Lambda of string * term;;

let rec level1 str =
  (
    ((level2 ++ level2) >> (fun (t1, t2) -> App (t1, t2)))
    || level2
  ) str
and level2 str =
  (
    ((a "!" ++ var ++ a "." ++ level1) >> 
	(fun (((_, v),_),t) -> Lambda (v, t)))
    || ((a "(" ++ level1 ++ a ")") >>
	   (fun ((_,t),_) -> t))
    || (var >> (fun v -> Var v))
  ) str
and var str =
  some (fun s -> (s >= "a" && s <= "z")) str;;
    

let rec lex = 
  function
    | " " :: t -> lex t
    | h :: t -> h :: lex t
    | [] -> [];;

let parse_term = fst $ level1 $ lex $ explode;;
let p = parse_term;;

let rec print_term fmt = function
  | Var v -> pp_print_string fmt v
  | App (t1, t2) ->
    begin
      pp_print_string fmt "(";
      print_term fmt t1;
      pp_print_string fmt " ";
      print_term fmt t2;
      pp_print_string fmt ")"
    end
  | Lambda (v, t) ->
    begin
      pp_print_string fmt "(!";
      pp_print_string fmt v;
      pp_print_string fmt ". ";
      print_term fmt t;
      pp_print_string fmt ")"
    end;;

let print_tm = print_term std_formatter;;
#install_printer print_tm;;

let rec uniq = function
  | (h1 :: (h2 :: t)) when h1 = h2 -> uniq (h2 :: t)
  | h :: t -> h :: uniq t
  | [] -> [];;

let union l1 l2 = uniq (List.sort compare (l1 @ l2));;
let rec diff l1 l2 =
  match l1 with
    | h :: t -> if List.mem h l2 then diff t l2 else h :: diff t l2
    | [] -> [];;

let rec free_in v = function
  | Lambda (v2, t) -> v2 <> v && free_in v t
  | App (t1, t2) -> free_in v t1 or free_in v t2
  | Var v2 -> v = v2;;

let rec exists p = function
  | h :: t -> if p h then true else exists p t
  | [] -> false;;

let rec filter p = function
  | h :: t -> if p h then h :: filter p t else filter p t
  | [] -> [];;

let rec variant avoid v =
  if not (exists (free_in v) avoid) then v else
    variant avoid (v ^ "'");;

let rec frees = function
  | Var v -> [v]
  | App (t1, t2) -> union (frees t1) (frees t2)
  | Lambda (v, t) -> diff (frees t) [v];;

let rec rev_assocd x list d =
  match list with
    | [] -> d
    | (a, y) :: t ->
      if x = y then a else rev_assocd x t d;;

let rec subst ilist tm =
  match tm with
    | Var v -> rev_assocd v ilist tm
    | App (t1, t2) -> App (subst ilist t1, subst ilist t2)
    | Lambda (v, s) ->
      let ilist' = filter (fun (t,x) -> x <> v) ilist in
      if ilist' = [] then tm else
	let s' = subst ilist' s in
	if exists (fun (t,x) -> free_in v t & free_in x s) ilist' then
	  let v' = variant [s'] v in
	  Lambda (v', subst ((Var v',v) :: ilist') s)
	else Lambda (v, s');;

let rec alpha v2 tm =
  match tm with
    | Lambda (v, t) ->
      if v = v2 then tm else
	if free_in v2 t then
	  failwith ("alpha: " ^ v2 ^ " is free in the abstraction body")
	else
	  Lambda (v2, subst [Var v2, v] t)
    | _ -> failwith "alpha: not lambda";;

let beta0 = function
  | App (Lambda (v, x), y) -> subst [y, v] x
  | _ -> failwith "beta";;

let rec beta1 = function
  | App (Lambda (v, x), y) -> subst [y, v] x
  | Lambda (v, t) -> Lambda (v, beta1 t)
  | App (t1, t2) -> 
    begin
      try App (beta1 t1, t2) with Failure _ -> App (t1, beta1 t2)
    end
  | _ -> failwith "beta1";; 

let rec beta tm =
  try
    let tm' = beta1 tm in
    beta tm'
  with Failure _ -> tm;;

let eta = function
  | Lambda (v, App (t, Var v2)) when v = v2 & not (free_in v t) -> t
  | _ -> failwith "eta";;

	 

let church =
  let f = Var "f" in
  let x = Var "x" in
  let rec iter n =
    if n > 0 then App (f, iter (n - 1)) else x in
  fun n ->
    Lambda ("f", Lambda ("x", iter n));;
  

let plus = p "!m. !n. !f. !x. (m f) ((n f) x)";;
let mult = p "!m. !n. !f. m (n f)";;
let exp = p "!m. !n. n m";;
let pred = p "!n. !f. !x. ((n (!g. !h. h (g f))) (!u. x)) (!u. u)";;
let minus = subst [pred, "p"] (p "!m. !n. (n p) m");;

let tm1 = App (App (plus, church 10), church 2);;
let tm2 = App (App (exp, church 3), church 3);;
let tm3 = App (pred, church 3);;
let tm4 = App (App (minus, church 3), church 1);;
beta tm1;;
beta tm2;;
beta tm3;;
beta tm4;;

let true_tm = p "!x. !y. x";;
let false_tm = p "!x. !y. y";;
let and_tm = p "!p. !q. (p q) p";;
let or_tm = p "!p. !q. (p p) q";;
let ite_tm = p "!p. !a. !b. (p a) b";;
let not_tm = p "!p. !a. !b. (p b) a";;
let is_zero = subst [false_tm, "f"; true_tm, "t"] (p "!n. (n (!x. f)) t");;

let y_comb = p "!g. (!x. g (x x)) (!x. g (x x))";;
let g_tm = subst [ite_tm, "i"; is_zero, "z"; church 1, "o"; mult, "m"; pred, "p"]
  (p "!r. !n. ((i (z n)) o) ((m n) (r (p n)))");;

let fact = App (y_comb, g_tm);;
beta (App (fact, church 3));;
