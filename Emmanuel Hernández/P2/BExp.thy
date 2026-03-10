theory BExp imports AExp begin

subsubsection \<open>Expresiones booleanas\<close>

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

(* IMP es un lenguaje que e esta modelando y es de tipo imperativo, esto porque esta basado en la mutabilidad*)

thm bexp.distinct
thm bexp.induct

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s  = (\<not> bval b s)" |
"bval (And b1 b2) s  = (bval b1 s \<and> bval b2 s)" |
"bval (Less e1 e2) s = (aval e1 s < aval e2 s)"

value "bval (Less (V ''x'') (Plus (N 3) (V ''y'')))
        <''x'' := 3, ''y'' := 1>"

section \<open>Optimizición\<close>

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)" |
"less e1 e2 = Less e1 e2"

lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
  by (induction a1 a2 rule: less.induct) auto



  term "True"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and x (Bc True) = x" |
"and (Bc True) x = x" |
"and x (Bc False) = Bc False" |
"and (Bc False) x = Bc False" |
"and b1 b2 = And b1 b2"

lemma [simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
  by (induction b1 b2 rule: and.induct) auto


fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc x) = Bc (\<not> x)" |
"not b = Not b"

lemma bval_not [simp]: "bval (not b) s = (\<not> bval b s)"
  by (induction b, auto)

text \<open>Optimización de bexp\<close>

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

value "bsimp (And (Less (N 0) (N 1)) b)"
value "bsimp (And (Less (N 1) (N 0)) (Bc True))"

lemma bval[simp]: "bval (bsimp b) s = bval b s"
  by (induction b, auto)

end