module type Core_type =
  sig
    type thm = private Thm of string
    val dest_thm : thm -> string
    val rule_par : thm -> thm
    val rule_cat : thm -> thm -> thm
    val axiom : thm
  end;;

module Core : Core_type = struct
  type thm = Thm of string;;

  let dest_thm = function Thm str -> str;;

  let rule_par th = Thm ("(" ^ dest_thm th ^ ")");;
  let rule_cat th1 th2 =
    Thm (dest_thm th1 ^ dest_thm th2);;
  
  let axiom = Thm "";;
end;;

open Core;;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;

let derive str =
  let rec rules list =
    match list with
      | [] | ")" :: _ -> axiom, list
      | "(" :: t ->
	begin
	  let th1, rest1 = rules t in
	  match rest1 with
	    | ")" :: t ->
	      let th2, rest2 = rules t in
	      rule_cat (rule_par th1) th2, rest2
	    | _ -> failwith ") expected"
	end
      | h :: _ -> failwith ("Bad symbol: " ^ h) in
  let th, rest = rules (explode str) in
  if rest <> [] then
    failwith "Bad string"
  else
    th;;
	

derive "(()(())())";;


type goal = string;;

type justification = thm list -> thm;;

type goalstate = goal list * justification;;

type goalstack = goalstate list;;

type refinement = goalstate -> goalstate;;

type tactic = goal -> goalstate;;

let tac_axiom : tactic = fun goal ->
  if goal = "" then ([], fun _ -> axiom) else failwith "tac_axiom";;

let tac_par : tactic =
  fun goal ->
    let n = String.length goal in
    if n < 2 then
      failwith "tac_par"
    else
      if (String.sub goal 0 1) <> "(" || (String.sub goal (n - 1) 1) <> ")" then
	failwith "tac_par"
      else
	([String.sub goal 1 (n - 2)],
	 function 
	   | [th] -> rule_par th
	   | _ -> failwith "tac_par justification"
	);;

let (tac_cat:int->tactic) =
  fun n goal ->
    let str1 = String.sub goal 0 n in
    let str2 = String.sub goal n (String.length goal - n) in
    ([str1; str2],
     function
       | [th1; th2] -> rule_cat th1 th2
       | _ -> failwith "tac_cat justification"
    );;

let (tac_all:tactic) =
  fun goal -> ([goal], fun ths -> List.hd ths);;



let current_goalstack = ref ([]:goalstack);;

let set_goal goal =
  current_goalstack := [[goal], fun list -> List.hd list];
  !current_goalstack;;

let top_thm() =
  match !current_goalstack with
    | ([], f) :: _ -> f []
    | _ -> failwith "top_thm";;

let (refine:refinement->goalstack) =
  fun r ->
    match !current_goalstack with
      | [] -> failwith "No current goal"
      | (h :: t) as l ->
	let res = r h :: l in
	current_goalstack := res;
	!current_goalstack;;

let rec chop_list n list =
  if n <= 0 then [], list
  else 
    match list with
      | [] -> [], []
      | h :: t ->
	let l1, l2 = chop_list (n - 1) t in
	h :: l1, l2;;

let (by:tactic->refinement) =
  fun tac (goals, just) ->
    match goals with
      | [] -> failwith "No goal set"
      | g :: ogls ->
	let (subgoals, subjust) = tac g in
	let n = List.length subgoals in
	let just' ths =
	  let cths, oths = chop_list n ths in
	  let sths = (subjust cths) :: oths in
	  just sths in
	subgoals @ ogls, just';;

let (prove:string * (tactic list) -> thm) =
  fun (goal, tacs) ->
    let state0 = ([goal], fun ths -> List.hd ths) in
    let (gls, just) = List.fold_left (fun s tac -> by tac s) state0 tacs in
    if gls <> [] then
      failwith "Unsolved goals"
    else
      just [];;

let e tac = refine (by tac);;

let b() =
  current_goalstack := List.tl (!current_goalstack);
  !current_goalstack;;

let g = set_goal;;

let (print_goal:goal->unit) =
  fun goal ->
    let str = "\"" ^ goal ^ "\"" in
    Format.print_string str;;

let (print_goalstack:goalstack->unit) =
  function
    | [] -> Format.print_string "Empty goalstack"
    | (goals, _) :: _ ->
      List.iter 
	(fun goal -> Format.print_string "\n"; print_goal goal)
	(List.rev goals);;

#install_printer print_goalstack;;


g "(()())";;
e tac_par;;
e (tac_cat 1);;
b();;
e (tac_cat 2);;
e tac_par;;
e tac_axiom;;
e tac_par;;
e tac_axiom;;

top_thm();;

prove("(()())",
      [tac_par;
       tac_cat 2;
       tac_par;
       tac_axiom;
       tac_par;
       tac_axiom]);;

