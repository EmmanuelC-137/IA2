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

subsection \<open>Structural induction for type @{typ nat}\<close>

text \<open>Explicit:\<close>

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
  proof (induction n)
  show "?P 0" by simp
  next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text \<open>In more detail:\<close>

text \<open>In more detail:\<close>

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next 
  fix n assume IH: "?P n"
  have "\<Sum>{0..Suc n} = \<Sum>{0..n} + Suc n" by simp
  also have "... = n *(n+1) div 2 + Suc n" using IH by simp
  also have "... = (Suc n)*((Suc n)+1) div 2" by simp
  finally show "?P(Suc n)" .
qed


text \<open>Implicit\<close>

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof (induction n)
  print_cases
  case 0
  show ?case by simp
next
  case (Suc n)
thm Suc
  thus ?case by simp
qed

text \<open>Induction with \<open>\<Longrightarrow>\<close>:\<close>

lemma split_list: "x : set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
thm Cons.IH (*Induction hypothesis*)
thm Cons.prems (*Premises of the step case*)
thm Cons
  from Cons.prems have "x = a \<or> x : set xs" by simp
  thus ?case
  proof
    assume "x = a"
    hence "a#xs = [] @ x # xs" by simp
    thus ?thesis by blast 
  next
    assume "x : set xs"
    then obtain ys zs where "xs = ys @ x # zs" using Cons.IH by auto
    hence "a#xs = (a#ys) @ x # zs" by simp
    thus ?thesis by blast
  qed
qed

subsection "Computation induction"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0"|
"div2 (Suc(Suc n)) = div2 n + 1"

lemma "2 * div2 n \<le> n"
proof (induction n rule: div2.induct)
  case 1
  show ?case by simp
next  
  case 2
  show ?case by simp
next
  case (3 n)
  have "2 * div2 (Suc(Suc n)) = 2 * div2 n + 2" by simp
  also have "... \<le> n + 2" using "3.IH" by simp
  also have "... = Suc(Suc n)" by simp
  finally show ?case .
qed

text \<open>Note that \<open>3.IH\<close> is not valid name, it needs double quotes: \<open>"3.IH"\<close>.\<close>

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a (x # y # zs) = x # a # sep a (y # zs)" |
"sep a xs = xs"

thm sep.simps

lemma "map f (sep a xs) = sep (f a) (map f xs)"
proof (induction a xs rule:  sep.induct)
  print_cases
  case (1 a x y zs)
  thus ?case by simp
next
  case ("2_1" a)
  show ?case by simp
next
  case ("2_2" a v)
  show ?case by simp
qed



end
