theory T2_BExp
  imports T1_AExp
begin

subsection \<open>Expresiones booleanas\<close>

(*Constante booleana
negación en una op binaria
conjunción es una op binaria*
Las exp booleanas se estan definiendo en las mismas expresiones 
*)
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp

thm bexp.distinct
thm bexp.induct (*esquema de inducción estructural*)

(*función que evalua exp binarias*)
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc \<and> ) = v " |
"bval (Not b) s = ( (bval b s))" |
"bval (And b1 b2) s \<not>

section \<open>Optimización\<close>

(*5<4 \<Rightarrow> False*)
fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)" (*para núm naturales*)
"less e1 e2 = Less e1 e2" (*para los que no son nat*)
(*La optimización no altera la semantica del programa*)

lemma [simp]: "bval (less a1 a2) s = 
  (aval a1 s < aval a2 s)"
  by (induction a1 a2 rule: less.induct) auto

(*Para definición del and por ejmeplo x and true = x, true and x=x, x and false=false*)
fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and x (Bc True) = x" |
"and (Bc True) b = b" |
"and b (Bc False) = Bc False" |
"and (Bc False) b = Bc False" |
"and b1 b2 = And b1 b2" (*para todos los casos restantes*)

lemma [simp]: "bval (and a1 a2) s = 
  (aval a1 s   aval a2 s)"
  by (induction a1 a2 rule: And.induct) auto

(*simplificar not true=false, not false=true *)
fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc x) = Bc (\<not>x)" |
"not b = Not b"

lemma bval_not[simp]: "bval (not b) s = (\<not>bval b s)"
  by (induction b, auto) (*inducción estructural*)

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" | 
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

value "bsimp (And (Less (N 0) (N 1)) b)"
value "bsimp (And (Less (N 1) (N 0)) (Bc True))"

lemma bval[simp]: "bval (bsimp b) s = bval b s)"
  by (induction b, auto)

end
