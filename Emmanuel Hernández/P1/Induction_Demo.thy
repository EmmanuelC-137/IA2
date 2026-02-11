theory Induction_Demo
  imports Main
begin

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x#xs) = rev xs @ [x]"

fun intrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intrev [] ys = ys" |
"intrev (x#xs) ys = intrev xs (x # ys)"

value "intrev [1,2,3::nat] []"

lemma l1: "intrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
  by auto

lemma "intrev xs [] = rev xs"
  apply (induction xs)
  by (auto simp add: l1)

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep x [] = []" |
"sep x [a] = [a]" |
"sep x (a # b # xs) = a # x # sep x (b # xs)"

value "sep x [1,2,3::nat]"

value "map f [x,y,z]"

value "map (\<lambda>x. x * x) [1,2,3,4::nat]"

text \<open>Induccion comuacional\<close>

thm sep.induct

lemma "map f (sep a xs) = sep (f a) (map f xs)"
  apply (induction a xs rule: sep.induct)
  by auto

(* Esto no funciona porque los esquemas de inducion computacional
son existosos  en punto donde los argumentos son puras variables

lemma "map f (sep a xs) = sep (f a) (map f xs)"
  apply (induction "f a" "map f xs" rule: sep.induct)
  by auto

*)

(*  Remplazar constantes por variables en otras palabras cambiar de 
color azul a verde, esto con arbitrary o con un cuantificador
universal en la formula.  *)


(* 
  0 + n = n
  (suc m) + n = suc (m + n)
  (suc m <= suc n) = (m <= n)
  (0 <= n) = True 
*)

(*
  0 + suc 0 <= suc 0 + x
  suc 0 <= suc 0 + x
  suc 0 <= suc (0 + x)
  0 <= 0 + x
  True 
*)

end