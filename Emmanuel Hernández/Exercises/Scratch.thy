theory Scratch
imports Main
begin

datatype pbexp = VAR string | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NEG (VAR x)) = True" |
"is_nnf (NEG b) = False" |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

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

lemma no_or_dist_AND: "no_or b1 \<Longrightarrow> no_or b2 \<Longrightarrow> no_or (dist_AND b1 b2)"
  apply(induction b1 b2 rule: dist_AND.induct)
  apply auto
done

lemma is_dnf_NEG_no_or[simp]: "is_dnf (NEG b) \<Longrightarrow> no_or (NEG b)"
  apply(cases b)
  apply auto
done

lemma is_dnf_not_OR_no_or[simp]: "is_dnf b \<Longrightarrow> (\<forall>x y. b \<noteq> OR x y) \<Longrightarrow> no_or b"
  apply(cases b)
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

lemma is_nnf_NEG_is_dnf[simp]: "is_nnf (NEG b) \<Longrightarrow> is_dnf (NEG b)"
  apply(cases b)
  apply auto
done

lemma is_nnf_dnf_of_nnf: "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply(induction b)
  apply (simp_all add: is_dnf_dist_AND)
done

end
