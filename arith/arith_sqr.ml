#load "nums.cma";;

open Big_int;;
open Num;;
open List;;

let print_big_int n = Format.pp_print_string Format.std_formatter (string_of_big_int n);;

#install_printer print_big_int;;

let num0 = Int 0 and
    num1 = Int 1;;

let bits = 3;;
let base = int_of_num (power_num (Int 2) (Int bits));;
let d_max = base - 1;;
let base_num = Int base;;

assert (base > 4);;

let counter = ref 0;;
let tbl = Hashtbl.create 10;;

let reset () = 
  counter := 0;
  Hashtbl.clear tbl;;

let work op = 
  let _ = counter := !counter + 1 in 
  let _ =
    try
      let t = Hashtbl.find tbl op in
      t := !t + 1
    with Not_found -> Hashtbl.add tbl op (ref 1) in
  ();;

let report =
  let fmt = Format.std_formatter in
  let p = Format.pp_print_string fmt in
  let nl = Format.pp_print_newline fmt in
  let print op t =
    p (Format.sprintf "%s: %d" op !t); nl() in
  fun () ->
    Hashtbl.iter print tbl;;

type nat = Z | D of int * nat;;

let rec num_of_nat = function
  | Z -> num0
  | D (i, n) -> 
    base_num */ num_of_nat n +/ Int i;;
    
let nat_of_num =
  let rec mk n =
    if sign_num n <= 0 then Z 
    else
      let m = mod_num n base_num in
      D (int_of_num m, mk (quo_num n base_num))
  in
  fun n ->
    if sign_num n < 0 then failwith "nat_of_num: Negative argument"
    else mk n;;

let nat_of_int i = nat_of_num (Int i);;


let rec suc_nat n =
  let _ = work "suc" in
  match n with
    | Z -> D (1, Z)
    | D (i, m) ->
      if i < d_max then
	D (i + 1, m)
      else
	D (0, suc_nat m);;

let rec add_nat n m =
  let _ = work "add" in
  match (n, m) with
    | (Z, _) -> m
    | (_, Z) -> n
    | (D (i, x), D (j, y)) ->
      let k = i + j in
      if k < base then
	D (k, add_nat x y)
      else
	D (k - base, suc_nat (add_nat x y));;

let sub2_nat n m =
  let _ = work "sub" in
  let n' = num_of_nat n and
      m' = num_of_nat m in
  let d' = n' -/ m' in
  if sign_num d' < 0 then
    let d = nat_of_num (minus_num d') in
    let _ = add_nat d n in 
    true, d
  else
    let d = nat_of_num d' in
    let _ = add_nat d m in 
    false, d;;

(* Bit shift operations *)
let mul2_nat =
  let rec mul2 bit a =
    let _ = work "mul2" in
    match a with
      | Z -> if bit = 1 then D (1, Z) else Z
      | D (i, m) ->
	let i' = (i lsl 1) lor bit in
	if i' < base then
	  D (i', mul2 0 m)
	else
	  D (i' land (base - 1), mul2 1 m)
  in
  mul2 0;;
  
let rec div2_nat a =
  let _ = work "div2" in
  match a with
    | Z -> Z
    | D (i, m) ->
      begin
	match m with
	  | Z -> 
	    let i' = i lsr 1 in
	    if i' = 0 then Z else D (i', Z)
	  | D (j, n) ->
	    let i' = (i lor ((j land 1) lsl bits)) lsr 1 in
	    D (i', div2_nat m)
      end;;

let rec div4_nat a =
  let _ = work "div4" in
  match a with
    | Z -> Z
    | D (i, m) ->
      begin
	match m with
	  | Z ->
	    let i' = i lsr 2 in
	    if i' = 0 then Z else D (i', Z)
	  | D (j, n) ->
	    let i' = (i lor ((j land 3) lsl bits)) lsr 2 in
	    D (i', div4_nat m)
      end;;


(* Multiplies (a:nat) and (j:int) *)
let rec mul1_nat a j =
  let _ = work "mul1" in
  match a with
    | Z -> Z
    | D (0, m) ->
      D (0, mul1_nat m j)
    | D (i, m) ->
      let k = i * j in
      if k < base then
	D (k, mul1_nat m j)
      else
	let q = k / base in
	let p = k - q * base in
	let prod = mul1_nat m j in
	D (p, add_nat (D (q, Z)) prod);;

(* Multiplies (a:nat) and (b:nat) *)
let rec mul_nat a b =
  let _ = work "mul" in
  match (a, b) with
    | (Z, _) -> Z
    | (_, Z) -> Z
    | (D (0, m), _) -> D (0, mul_nat m b)
    | (_, D (0, n)) -> D (0, mul_nat a n)
    | (D (i, m), D (j, n)) ->
      if m = Z then
	if n = Z then
	  let k = i * j in
	  if k < base then
	    D (k, Z)
	  else
	    let q = k / base in
	    let p = k - q * base in
	    D (p, D (q, Z))
	else
	  mul1_nat b i
      else if n = Z then
	mul1_nat a j
      else
	let k = i * j in
	let q = k / base in
	let p = k - q * base in
	let prod = mul_nat m n and
	    prod1 = mul1_nat m j and
	    prod2 = mul1_nat n i in
	let s1 = add_nat (D (q, prod)) prod1 in
	let s2 = add_nat s1 prod2 in
	D (p, s2);;


let rec square_nat a =
  let _ = work "sqr" in
  match a with
    | Z -> Z
    | D (0, m) -> D (0, D (0, square_nat m))
    | D (i, m) ->
      let k = i * i in
      let q = k / base in
      let p = k - q * base in
      let sqr = square_nat m in
      let prod = mul2_nat (mul1_nat m i) in
      D (p, add_nat (D (q, sqr)) prod);;

let rec square2_nat a =
  let _ = work "sqr2" in
  match a with
    | Z -> Z
    | D (i, m) ->
      begin
	match m with
	  | Z ->
	    let k = i * i in
	    if k < base then
	      D (k, Z)
	    else
	      let q = k / base in
	      let p = k - q * base in
	      D (p, D (q, Z))
	  | D (j, n) ->
	    let t = base * j + i in
	    let k = t * t in
	    let b2 = base * base in
	    let b3 = b2 * base in
	    let y = k / b3 in
	    let t = k - b3 * y in
	    let x = t / b2 in
	    let t = t - b2 * x in
	    let q = t / base in
	    let p = t - base * q in
	    let sqr = square2_nat n in
	    let prod1 = mul2_nat (mul1_nat n j) in
	    let prod2 = mul2_nat (mul1_nat n i) in
	    let s1 = add_nat (D (y, sqr)) prod1 in
	    let s2 = add_nat (D (x, s1)) prod2 in
	    (*
	    let k = 2 * (j * base + i) in
	    let prod = mul_nat n (nat_of_int k) in
	    let s2 = add_nat (D (x, D (y, sqr))) prod in
	    *)
	    D (p, D (q, s2))
      end;;


let mul_sqr1_nat a b =
  let _ = work "mul_sqr1" in
  let ab = add_nat a b in
  let ab_sqr = square2_nat ab and
      a_sqr = square2_nat a and
      b_sqr = square2_nat b in
  let _, d1 = sub2_nat ab_sqr a_sqr in
  let _, d2 = sub2_nat d1 b_sqr in
  div2_nat d2;;

let mul_sqr2_nat a b =
  let _ = work "mul_sqr2" in
  let p_ab = add_nat a b and
      _, m_ab = sub2_nat a b in
  let p_sqr = square2_nat p_ab and
      m_sqr = square2_nat m_ab in
  let _, d = sub2_nat p_sqr m_sqr in
  div4_nat d;;
      

let n1 = nat_of_int 100 and
    n2 = nat_of_int 71 in
num_of_nat (mul_nat n1 n2),
num_of_nat (mul_sqr1_nat n1 n2),
num_of_nat (mul_sqr2_nat n1 n2),
num_of_nat (square_nat n1),
num_of_nat (square_nat n2),
num_of_nat (square2_nat n1),
num_of_nat (square2_nat n2),
num_of_nat (div4_nat n1),
num_of_nat (div4_nat n2);;

let n1 = nat_of_int 1232000 and
    n2 = nat_of_int 71434330;;

reset();;
mul_nat n1 n2;;
!counter;; (* 143 *)
report();;

reset();;
mul_sqr1_nat n1 n2;;
!counter;; (* 380 *)
report();;

reset();;
mul_sqr2_nat n1 n2;;
!counter;; (* 391 *)
report();;

reset();;
mul_nat n2 n2;;
!counter;; (* 131 *)
report();;

reset();;
square_nat n2;;
!counter;; (* 97 *)
report();;

reset();;
square2_nat n2;;
!counter;; (* 68 *)
report();;


reset();;
mul_nat n2 (nat_of_int 2);;
!counter;; (* 14 *)
report();;

reset();;
mul2_nat n2;;
!counter;; (* 10 *)
report();;

