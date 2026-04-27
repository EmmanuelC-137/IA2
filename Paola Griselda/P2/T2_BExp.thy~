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
"bval (Bc \<and> ) =  " |

leer el capitulo de claseg