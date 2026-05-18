theory Isar_Induction_Demo
  imports Main
begin

section "Case distinction and induction"

subsection "Case distinction"

text \<open>Explicit: \<close>

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []" thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

text \<open>Implicit: \<close>

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

subsubsection \<open>Structural induction for type @{typ nat}\<close>

text \<open>Explicit: \<close>
lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed


end