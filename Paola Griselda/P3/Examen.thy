theory Examen
imports Main
begin

text \<open>Ejercicio 1\<close>

inductive palindrome :: "'a list \<Rightarrow> bool" where
"palindrome []" |
"palindrome [x]" |
"palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction)
  by(auto)




text \<open>Ejercicio 2\<close>

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] y = 0" |
"count (x#xs) y = (if x=y then Suc(count xs y) else count xs y)"

theorem "count xs x \<le> length xs"


text \<open>Ejercicio 3\<close>

datatype aexp = N int | V string | Plus aexp aexp

lemma "optimal (asimp_const a)"
  by 

end