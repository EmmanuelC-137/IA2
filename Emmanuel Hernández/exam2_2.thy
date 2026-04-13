theory exam2_2
imports Main

begin

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"


lemma itadd_thm: "itadd m n = m + n"

apply (induction m arbitrary: n)
apply auto
done


datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" |
"eval (Add e1 e2) x = eval e1 x + eval e2 x" |
"eval (Mult e1 e2) x = eval e1 x * eval e2 x"

fun simp_add :: "exp => exp" where
"simp_add (Add e (Const n)) = (if n = 0 then simp_add e else Add e (Const n))" |
"simp_add (Add (Const n) e) = (if n = 0 then simp_add e else Add (Const n) e)" |
"simp_add (Add e1 e2) = Add (simp_add e1) (simp_add e2)" |
"simp_add (Mult e1 e2) = Mult (simp_add e1) (simp_add e2)" |
"simp_add e = e"

lemma simp_add_correct: "eval (simp_add e) x = eval e x"

apply (induction e rule: simp_add.induct)
apply auto
done



end