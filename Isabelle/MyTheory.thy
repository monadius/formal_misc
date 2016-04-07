theory MyTheory
imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02: "add m 0 = m"
apply(induction m)
apply(auto)
done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (y # ys) = (if x = y then 1 else 0) + count x ys"

lemma count_le_length: "count x ys \<le> length ys"
apply(induction ys)
apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = 2 + double n"

lemma add_Suc2 [simp]: "add a (Suc b) = Suc (add a b)"
apply(induction a)
apply(auto)
done

lemma double_eq_add: "double m = add m m"
apply(induction m)
apply(auto)
done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] y = [y]" |
"snoc (x # xs) y = x # snoc xs y"

lemma length_snoc: "length (snoc xs y) = Suc (length xs)"
apply(induction xs)
apply(auto)
done

fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = Suc n + sum n"

lemma sum_eq: "sum n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
done

(* 2.3 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = contents l @ [a] @ contents r"

fun treesum :: "nat tree \<Rightarrow> nat" where
"treesum Tip = 0" |
"treesum (Node l a r) = treesum l + a + treesum r"

lemma treesum_eq: "treesum t = listsum (contents t)"
apply(induction t)
apply(auto)
done

datatype 'a tree2 = Leaf 'a | Node2 "'a tree2" "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Leaf x) = Leaf x" |
"mirror2 (Node2 l r) = Node2 (mirror2 r) (mirror2 l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf x) = [x]" |
"pre_order (Node2 l r) = pre_order l @ pre_order r"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf x) = [x]" |
"post_order (Node2 l r) = post_order r @ post_order l"

lemma pre_post_order: "pre_order (mirror2 t) = post_order t"
apply(induction t)
apply(auto)
done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x # xs) = x # a # intersperse a xs"

lemma intersperse_lemma: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction a xs rule: intersperse.induct)
apply(auto)
done

(* 2.4 *)

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

lemma "itrev xs ys = rev xs @ ys"
apply (induction xs arbitrary: ys)
apply auto
done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = add m n"
apply (induction m arbitrary: n)
apply auto
done

(* 2.5 *)

datatype tree0 = Leaf | Node0 tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1" |
"nodes (Node0 l r) = nodes l + nodes r + 1"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node0 t t)"

lemma ex2_10: "nodes (explode n t) = 2 ^ n * (nodes t + 1) - 1"
apply(induction n arbitrary: t)
apply(auto simp add: algebra_simps)
done

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" | 
"eval (Add e1 e2) x = eval e1 x + eval e2 x" |
"eval (Mult e1 e2) x = eval e1 x * eval e2 x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (a # as) x = a + x * evalp as x"

fun add_plist :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"add_plist [] ys = ys" |
"add_plist xs [] = xs" |
"add_plist (x # xs) (y # ys) = (x + y) # add_plist xs ys"

definition cmul_plist :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"cmul_plist c xs = map (op * c) xs"

fun mul_plist :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mul_plist [] ys = []" |
"mul_plist xs [] = []" |
"mul_plist (x # xs) ys = add_plist (cmul_plist x ys) (0 # mul_plist xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const c) = [c]" |
"coeffs (Add e1 e2) = add_plist (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = mul_plist (coeffs e1) (coeffs e2)"

lemma evalp_add [simp]: "evalp (add_plist as bs) x = evalp as x + evalp bs x"
apply(induction as bs rule: add_plist.induct)
apply(auto simp add: algebra_simps)
done

lemma evalp_cmul [simp]: "evalp (cmul_plist c as) x = c * evalp as x"
apply (induction as)
apply (auto simp add: cmul_plist_def algebra_simps)
done

lemma evalp_mul [simp]: "evalp (mul_plist a b) x = evalp a x * evalp b x"
apply(induction a b rule: mul_plist.induct)
apply(auto simp add: algebra_simps)
done

lemma ex2_11: "evalp (coeffs e) x = eval e x"
apply(induction e)
apply(auto)
done

(* 3.2 *)

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l a r) = set l \<union> {a} \<union> set r"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l a r) = ((\<forall>x \<in> set l. x \<le> a) \<and> (\<forall>x \<in> set r. a \<le> x) \<and> ord l \<and> ord r)"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins y Tip = Node Tip y Tip" |
"ins y (Node l a r) = 
  (if (y = a) then (Node l a r) else
    (if y < a then (Node (ins y l) a r) else (Node l a (ins y r))))"

lemma ex3_1_set_ins: "set (ins x t) = {x} \<union> set t"
apply(induction t)
apply(auto)
done

lemma ex3_1_ord_ins: "ord t \<Longrightarrow> ord (ins x t)"
apply(induction t)
apply(auto simp add: ex3_1_set_ins)
done

(* 3.3 *)
lemma "\<forall>x. \<exists>y. x = y"
by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
by auto

lemma "\<lbrakk>\<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A\<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n"
by fastforce

lemma "\<lbrakk>\<forall>x y. T x y \<or> T y x;
        \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
        \<forall>x y. T x y \<longrightarrow> A x y\<rbrakk>
        \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast

lemma "\<lbrakk>xs @ ys = ys @ xs; length xs = length ys\<rbrakk> \<Longrightarrow> xs = ys"
by (metis append_eq_conv_conj)

lemma "\<lbrakk>(a::nat) \<le> x + b; 2 * x < c\<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2 * b + c"
by arith

(* 3.4 *)

lemma "\<lbrakk>(a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e\<rbrakk> \<Longrightarrow> a \<le> e"
by (blast intro: le_trans)

thm conjI[OF refl[of "a"] refl[of "b"]]

lemma "Suc (Suc (Suc a)) \<le> b \<Longrightarrow> a \<le> b"
by (blast dest: Suc_leD)

thm conjI[OF refl]

(* 3.5 *)

inductive ev :: "nat \<Rightarrow> bool" where
ev0:  "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun even :: "nat \<Rightarrow> bool" where
"even 0 = True" |
"even (Suc 0) = False" |
"even (Suc (Suc n)) = even n"

lemma "ev n \<Longrightarrow> even n"
apply(induction rule:ev.induct)
apply(auto)
done

lemma "ev (Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)
apply(rule evSS)
by (rule ev0)

declare ev.intros[simp,intro]

lemma "even n \<Longrightarrow> ev n"
apply(induction n rule: even.induct)
by simp_all

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(assumption)
apply(metis step)
done

inductive palindrome :: "'a list \<Rightarrow> bool" where
pal_nil:  "palindrome []" |
pal_sing: "palindrome [x]" |
pal_step: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma ex3_2: "palindrome xs \<Longrightarrow> rev xs = xs"
apply(induction rule:palindrome.induct)
apply(auto)
done

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_right: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
apply(induction rule:star.induct)
apply(auto simp add: star.intros)
done

lemma ex3_3: "star' r x y \<Longrightarrow> star r x y"
apply(induction rule:star'.induct)
apply(rule refl)
apply(simp add:star_right)
done

lemma star'_left: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
apply(induction rule:star'.induct)
apply(auto simp add: star'.intros)
apply(rule step')
apply(auto simp add: star'.intros)
done

lemma ex3_3': "star r x y \<Longrightarrow> star' r x y"
apply(induction rule:star.induct)
apply(rule refl')
apply(simp add:star'_left)
done

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_refl: "iter r 0 x x" |
iterS:     "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma ex3_4: "iter r n x y \<Longrightarrow> star r x y"
apply(induction rule:iter.induct)
apply(auto simp add:star.intros)
done

lemma ex3_4': "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
apply(induction rule:star.induct)
apply(rule exI[of _ "0"])
apply(rule iter_refl)
apply(metis iterS)
done

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S_empty: "S []" |
S_step1: "S w \<Longrightarrow> S (a # w @ [b])" |
S_step2: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_empty: "T []" |
T_step:  "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ (a # w2 @ [b]))"

lemma ex3_5: "T w \<Longrightarrow> S w"
apply(induction rule:T.induct)
apply(auto simp add:S.intros)
done

lemma T_append_nil: "T ([] @ w) \<Longrightarrow> T w"
by simp

lemma T_step1: "T w \<Longrightarrow> T (a # w @ [b])"
apply (rule T_append_nil)
apply (rule T_step)
apply (rule T_empty)
apply (assumption)
done

(*
lemma "S w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> \<exists>u. S u \<and> w = a # u @ [b]"
--apply(induction rule:S.induct)
--apply(auto)
*)


lemma "T w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> \<exists>x y. T x \<and> T y \<and> w = x @ (a # y @ [b])"
apply(induction rule:T.induct)
apply(auto)
done

(*
lemma ex3_5': "S w \<Longrightarrow> T w"
apply(induction rule:S.induct)
apply(rule T_empty)
apply(simp add:T_step1)
*)


