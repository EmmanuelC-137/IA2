theory Isar_Induction_Demo
imports Main
begin 

section \<open>Case distinction and induction\<close>

subsection "Case distinction"

text \<open>Explicit:\<close>

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []" thus ?thesis by simp
next 
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

text \<open>Implicit:\<close>

lemma "length(tl xs) = length xs - 1"
proof (cases xs) 
  print_cases
  case Nil
  thm Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thm Cons
  thus ?thesis by simp
qed

end
