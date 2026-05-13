theory Scratch
imports Main
begin

datatype aexp = N int | V string | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> (string \<Rightarrow> int) \<Rightarrow> int" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(* Ex 3.3 *)
fun subst :: "string \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if x = y then a else V y)" |
"subst x a (Plus a1 a2) = Plus (subst x a a1) (subst x a a2)"

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
apply(induction e)
apply auto
done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
apply(induction e)
apply auto
done

(* Ex 3.9 *)
datatype pbexp = VAR string | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NEG b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NEG (VAR x)) = True" |
"is_nnf (NEG b) = False" |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

fun push_neg :: "pbexp \<Rightarrow> pbexp"
and nnf :: "pbexp \<Rightarrow> pbexp" where
"push_neg (VAR x) = NEG (VAR x)" |
"push_neg (NEG b) = nnf b" |
"push_neg (AND b1 b2) = OR (push_neg b1) (push_neg b2)" |
"push_neg (OR b1 b2) = AND (push_neg b1) (push_neg b2)" |
"nnf (VAR x) = VAR x" |
"nnf (NEG b) = push_neg b" |
"nnf (AND b1 b2) = AND (nnf b1) (nnf b2)" |
"nnf (OR b1 b2) = OR (nnf b1) (nnf b2)"

lemma pbval_push_neg_nnf:
  "pbval (push_neg b) s = (\<not> pbval b s)"
  "pbval (nnf b) s = pbval b s"
apply(induction b and b rule: push_neg_nnf.induct)
apply auto
done

lemma is_nnf_push_neg_nnf:
  "is_nnf (push_neg b)"
  "is_nnf (nnf b)"
apply(induction b and b rule: push_neg_nnf.induct)
apply auto
done

fun no_or :: "pbexp \<Rightarrow> bool" where
"no_or (VAR x) = True" |
"no_or (NEG (VAR x)) = True" |
"no_or (NEG b) = False" |
"no_or (AND b1 b2) = (no_or b1 \<and> no_or b2)" |
"no_or (OR b1 b2) = False"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NEG (VAR x)) = True" |
"is_dnf (NEG b) = False" |
"is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)" |
"is_dnf (AND b1 b2) = (no_or b1 \<and> no_or b2)"

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dist_AND (OR b1 b2) b3 = OR (dist_AND b1 b3) (dist_AND b2 b3)" |
"dist_AND b1 (OR b2 b3) = OR (dist_AND b1 b2) (dist_AND b1 b3)" |
"dist_AND b1 b2 = AND b1 b2"

lemma pbval_dist_AND: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
apply(induction b1 b2 rule: dist_AND.induct)
apply auto
done

lemma no_or_dist_AND: "no_or b1 \<Longrightarrow> no_or b2 \<Longrightarrow> no_or (dist_AND b1 b2)"
apply(induction b1 b2 rule: dist_AND.induct)
apply auto
done

lemma is_dnf_dist_AND: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
apply(induction b1 b2 rule: dist_AND.induct)
apply (simp_all add: no_or_dist_AND)
done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NEG b) = NEG b" |
"dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)" |
"dnf_of_nnf (AND b1 b2) = dist_AND (dnf_of_nnf b1) (dnf_of_nnf b2)"

lemma pbval_dnf_of_nnf: "pbval (dnf_of_nnf b) s = pbval b s"
apply(induction b)
apply (simp_all add: pbval_dist_AND)
done

lemma is_nnf_dnf_of_nnf: "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
apply(induction b)
apply (simp_all add: is_dnf_dist_AND)
done

end
