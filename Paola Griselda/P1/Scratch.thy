theory 1_AExp
  imports
begin

subsection \<open>\<close>

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(*Los strings en Isabelle se denotan por dos comillas simples*)

(*Defiición de la esructura de datos con la que vamos a representar las estructuras numericas*)
(*Sintacticamente los entyero son diferentes de las cadenas y de las expresiones*)
datatype aexp = N int | V vname | Plus aexp aexp
thm aexp.distinct

(*Recibe un estado, función *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s "

end