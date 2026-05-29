theory ExamenFinal
  imports Main
begin

text \<open>Pregunta 4\<close>
datatype aexp = N int | V string | Plus aexp aexp
fun optimal :: "aexp \<Rightarrow> bool" where 

text \<open>Pregunta 17\<close>
definition snoc :: "'a list \<Rightarrow>'a \<Rightarrow> 'a list" 

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (x#xs) a = x # snoc xs a"

text \<open>Pregunta 22\<close>
lemma "snoc xs a = xs @ [a]"
  apply (induction xs)
  apply (auto)

text \<open>Pregunta 20\<close>
(*lemma "mult x (suc y) = suma x (mult x y)"*)
lemma "suma a (suc b) = suc(suma a b)"
  apply(induction a)
apply (auto)
  

lemma "mult x (suc y) = suma x (mult x y)"
  apply(induction a)
  apply (auto)





 

