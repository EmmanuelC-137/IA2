theory Inductive_Demo
  imports Main
begin

text \<open>Definicion inductiva\<close>

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc (Suc n))"

text \<open>Reglas de Introducción\<close>
thm ev0 evSS

thm ev.intros
thm ev.cases
thm ev.induct

text \<open>Uso de las reglas de introducción\<close>
lemma "ev (Suc (Suc (Suc (Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

thm evSS[OF evSS [OF ev0]]

text \<open>Definicion recursiva de numeros pares\<close>

fun env :: "nat \<Rightarrow> bool" where
"env 0 = True" |
"env (Suc 0) = False" |
"env (Suc (Suc n)) = env n"

text \<open>Aplicacion de la regla de induccion\<close>

lemma "ev n \<Longrightarrow> env n"
  by(induction n rule: ev.induct, simp_all)

lemma "ev n \<Longrightarrow> \<exists>k. n = 2 * k"

end