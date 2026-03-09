theory BExp imports AExp begin

subsubsection \<open>Expresiones booleanas\<close>

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

thm bexp.distinct
thm bexp.induct

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc n) s = (if n = 0) "


end