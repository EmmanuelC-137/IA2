theory cap_2
  imports Main
begin

section "Capitulo 2"

text \<open> Exercise 2.1. Use the value command to evaluate the following expressions:
"1 + (2::nat)", "1 + (2::int)", "1 − (2::nat)" and "1 − (2::int)". \<close>

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"



text \<open> Exercise 2.2. Start from the definition of add given above. Prove that add
is associative and commutative. Define a recursive function double :: nat \<Rightarrow>
nat and prove double m = add m m. \<close>

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02 [simp]: "add m 0 = m"
apply(induction m)
apply(auto)
done

lemma add_assoc: "add (add m n) p = add m (add n p)"
apply(induction m)
apply(auto)
done

lemma add_Suc2 [simp]: "add m (Suc n) = Suc(add m n)"
apply(induction m)
apply(auto)
done

lemma add_comm: "add m n = add n m"
apply(induction m)
apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc(Suc(double m))"

lemma double_add: "double m = add m m"
apply(induction m)
apply(auto)
done



text \<open> Exercise 2.3. Define a function count :: a \<Rightarrow> a list \<Rightarrow> nat that counts the
number of occurrences of an element in a list. Prove count x xs length xs. \<close>


fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (y # ys) = (if x = y then Suc (count x ys) else count x ys)"

lemma count_le_length: "count x xs \<le> length xs"
apply(induction xs)
apply(auto)
done



text \<open>Exercise 2.4. Define a recursive function snoc :: a list \<Rightarrow> a \<Rightarrow> a list
that appends an element to the end of a list. With the help of snoc define
a recursive function reverse :: a list \<Rightarrow> a list that reverses a list. Prove
reverse (reverse xs) = xs. \<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = x # (reverse xs)"
apply(induction xs)
apply(auto)
done

lemma reverse_reverse: "reverse (reverse xs) = xs"
apply(induction xs)
apply(auto)
done



text \<open> Exercise 2.5. Define a recursive function sum_upto :: nat \<Rightarrow> nat such that
sum_upto n = 0 + ... + n and prove sum_upto n = n \<^emph> (n + 1) div 2. \<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = (Suc n) + sum_upto n"

lemma sum_upto: "sum_upto n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
done



text \<open>Exercise 2.6. Starting from the type a tree defined in the text, define a
function contents :: a tree \<Rightarrow> a list that collects all values in a tree in a list,
in any order, without removing duplicates. Then define a function sum_tree
:: nat tree \<Rightarrow> nat that sums up all values in a tree of natural numbers and
prove sum_tree t = sum_list (contents t) where sum_list is predefined by
the equations sum_list [] = 0 and sum_list (x # xs) = x + sum_list xs.\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l x r) = contents l @ [x] @ contents r"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l x r) = sum_tree l + x + sum_tree r"

lemma sum_tree_contents: "sum_tree t = sum_list (contents t)"
apply(induction t)
apply(auto)
done



text \<open>Exercise 2.7. Define the two functions pre_order and post_order of type
a tree \<Rightarrow> a list that traverse a tree and collect all stored values in the
respective order in a list. Prove pre_order (mirror t) = rev (post_order t).\<close>

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l x r) = x # (pre_order l @ pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l x r) = post_order l @ post_order r @ [x]"

lemma pre_post_order: "pre_order (mirror t) = rev (post_order t)"
apply(induction t)
apply(auto)
done



text \<open>Exercise 2.8. Define a function intersperse :: a \<Rightarrow> a list \<Rightarrow> a list such
that intersperse a [x1, ..., xn] = [x1, a, x2, a, ..., a, xn]. Now prove that
map f (intersperse a xs) = intersperse (f a) (map f xs).\<close>

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x # y # ys) = x # a # (intersperse a (y # ys))"

lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs rule: intersperse.induct)
apply(auto)
  done


text \<open>Exercise 2.9. Write a tail-recursive variant of the add function on nat:
itadd. Tail-recursive means that in the recursive case, itadd needs to call
itself directly: itadd (Suc m) n = itadd .... Prove itadd m n = add m n.\<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_add: "itadd m n = add m n"
apply(induction m arbitrary: n)
apply(auto)
done



text \<open>Exercise 2.10. Define a datatype tree0 of binary tree skeletons which do not
store any information, neither in the inner nodes nor in the leaves. Define a
function nodes :: tree0 \<Rightarrow> nat that counts the number of all nodes (inner
nodes and leaves) in such a tree. Consider the following recursive function:

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

Find an equation expressing the size of a tree after exploding it (nodes
(explode n t)) as a function of nodes t and n. Prove your equation. You
may use the usual arithmetic operators, including the exponentiation opera
tor “^”. For example, 2 ^ 2 = 4.
Hint: simplifying with the list of theorems algebra_simps takes care of
common algebraic properties of the arithmetic operators.\<close>

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = nodes l + nodes r + 1"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

lemma nodes_explode: "nodes (explode n t) = 2^n * nodes t + 2^n - 1"
apply(induction n arbitrary: t)
apply(auto simp add: algebra_simps)
done



text \<open>Exercise 2.11. Define arithmetic expressions in one variable over integers
(type int) as a data type:

datatype exp = Var | Const int | Add exp exp | Mult exp exp

Define a function eval :: exp \<Rightarrow> int \<Rightarrow> int such that eval e x evaluates e at the value x.
A polynomial can be represented as a list of coefficients, starting with the
constant. For example, [4, 2, − 1, 3] represents the polynomial 4+2x−x2+3x3.
Define a function evalp :: int list \<Rightarrow> int \<Rightarrow> int that evaluates a polynomial at
the given value. Define a function coeffs :: exp \<Rightarrow> int list that transforms an
expression into a polynomial. This may require auxiliary functions. Prove that
coeffs preserves the value of the expression: evalp (coeffs e) x = eval e x.
Hint: consider the hint in Exercise 2.10.\<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" |
"eval (Add e1 e2) x = eval e1 x + eval e2 x" |
"eval (Mult e1 e2) x = eval e1 x * eval e2 x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (c # cs) x = c + x * evalp cs x"

fun addp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"addp [] ys = ys" |
"addp xs [] = xs" |
"addp (x # xs) (y # ys) = (x + y) # addp xs ys"

fun multp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"multp [] ys = []" |
"multp (x # xs) ys = addp (map (\<lambda>z. x * z) ys) (0 # multp xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const c) = [c]" |
"coeffs (Add e1 e2) = addp (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = multp (coeffs e1) (coeffs e2)"

lemma evalp_addp [simp]: "evalp (addp p1 p2) x = evalp p1 x + evalp p2 x"
apply(induction p1 p2 rule: addp.induct)
apply(auto simp add: algebra_simps)
done

lemma evalp_map_mult [simp]: "evalp (map (\<lambda>z. y * z) p) x = y * evalp p x"
apply(induction p)
apply(auto simp add: algebra_simps)
done

lemma evalp_multp [simp]: "evalp (multp p1 p2) x = evalp p1 x * evalp p2 x"
apply(induction p1)
apply(auto simp add: algebra_simps)
done

theorem eval_coeffs: "evalp (coeffs e) x = eval e x"
apply(induction e)
apply(auto simp add: algebra_simps)
done

end