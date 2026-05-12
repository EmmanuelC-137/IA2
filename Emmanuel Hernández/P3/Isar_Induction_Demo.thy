theory Isar_Induction_Demo
  imports Main
begin

section "Case distinction and induction"

subsection "Case distinction"

text ‹Explicit: ›

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []" thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

text ‹Implicit: ›

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

subsubsection ‹Structural induction for type @{typ nat}›

text ‹Explicit: ›
lemma "∑{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text  ‹In more details: ›

lemma "∑{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume IH: "?P n"
  have "∑{0..Suc n} = ∑{0..n} + Suc n" by simp
  also have "... = n*(n+1) div 2 + Suc n" using IH by simp
  also have "... = (Suc n) * ((Suc n)+1) div 2" by simp
  finally show "?P(Suc n)" .
qed

text  ‹Implicit: ›

lemma "∑{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  print_cases
  case 0
  show ?case by simp
next
  case (Suc n)
  thm Suc
  thus ?case by simp
qed


text  ‹Induction with ‹\<Longrightarrow>›: ›

lemma split_list: "x: set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  thm Cons.IH (*Introduccion de hipotesis*)
  thm Cons.prems (*Premises of the step case*)
  thm Cons
  from Cons.prems have "x = a \<or> x: set xs" by simp
  thus ?case
  proof
    assume "x = a"
    hence "a#xs = [] @ x # xs" by simp
    thus ?thesis by blast
  next
    assume "x: set xs"
    then obtain ys zs where "xs = ys @ x # zs" using Cons.IH by auto
      hence "a#xs = (a#ys) @ x # zs" by simp
      thus ?thesis by blast
    qed
qed

end