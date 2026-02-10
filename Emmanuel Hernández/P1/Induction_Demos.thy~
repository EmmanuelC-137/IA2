theory Induction_Demos
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

end