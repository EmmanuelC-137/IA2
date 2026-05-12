theory cap_3
imports Main
begin

section "Capitulo 3"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus e1 e2) = 
  (case (asimp_const e1, asimp_const e2) of 
    (N x, N y) \<Rightarrow> N (x+y)
  | (e1, e2) \<Rightarrow> Plus e1 e2)"

text \<open>Exercise 3.1. To show that asimp_const really folds all subexpressions of
the form Plus (N i) (N j), define a function optimal :: aexp \<Rightarrow> bool that
checks that its argument does not contain a subexpression of the form Plus
(N i) (N j). Then prove optimal (asimp_const a).\<close>

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus e1 e2) = (optimal e1 \<and> optimal e2)"

theorem optimal_asimp_const: "optimal (asimp_const a)"
apply(induction a)
apply(auto split: aexp.split)
done



text \<open>Exercise 3.2. In this exercise we verify constant folding for aexp where we
sumupall constants, even if they are not next to each other. For example, Plus
(N 1) (Plus (V x) (N 2))becomesPlus (V x) (N 3).Thisgoesbeyondasimp.
Define a function full_asimp :: aexp \<Rightarrow> aexp that sums up all constants and
prove its correctness: aval (full_asimp a) s = aval a s.\<close>


text \<open>Exercise 3.3. Substitution is the process of replacing a variable by an ex
pression in an expression. Define a substitution function subst :: vname \<Rightarrow>
aexp \<Rightarrow> aexp \<Rightarrow> aexp such that subst x a e is the result of replacing every
occurrence of variable x by a in e. For example:

3 Case Study: IMP Expressions

subst x (N 3) (Plus (V x ) (V y )) = Plus (N 3) (V y )
Prove the so-called substitution lemma that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
aval (subst x a e) s = aval e (s(x := aval a s)). As a consequence prove
aval a1 s = aval a2 s =\<Rightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s.\<close>



end