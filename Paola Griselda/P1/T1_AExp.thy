theory T1_AExp
  imports Main
begin

subsection \<open>Expresiones Aritmeticas\<close>

type_synonym vname = string
type_synonym val = int
type_synonym state = vname \<Rightarrow> val

(*Los strings en Isabelle se denotan por dos comillas simples*)
value "''hola mundo'' "
(*Defiición de la esructura de datos con la que vamos a representar las estructuras numericas*)
(*Sintacticamente los entyero son diferentes de las cadenas y de las expresiones*)
datatype aexp = N int | V vname | Plus aexp aexp

thm aexp.distinct

(*Recibe un estado, función *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s "

value "aval (Plus(V ''x'') (N 5))
            (\<lambda>x. if x = ''x'' then 10 else 0)"

text \<open>El mismo estado pero usandno notación mas corta\<close>

value "aval (Plus(V ''x'') (V ''y''))
            (((\<lambda>x. 0 if x = ''x'' then 10 else 0)"

text \<open>De forma mas compacta\<close>

definition null_state ("<>") where
"null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds \<Rightarrow> 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= 
  "_Update (_State b) bs"

thm refl (*axioma t es igual a t para todo t*)

(*en la repersentación interna del lado derecho al lado izq sintacticamente son iguales*)
lemma "<a:=1, b:=2> = (<> (a:=1)) (b:=2::int)"
  by (rule refl)

text \<open>esta, se obtiene un 5 poque no coinciden los strings \<close>
value "aval (Plus (V ''x'') (N 5)) 

text \<open>Martes 03 de Marzo\<close>

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus e1 e2) = 
  (case (asimp_const e1, asimp_const e2) of
  (N x, N y) \<Rightarrow> N (x + y) |
  (e1, e2) \<Rightarrow> Plus e1 e2)"

value "asimp_const (Plus (V ''x'') (Plus (N 5) (N 6)"

theorem aval_asimp_const:
  "aval (asimp_const e) s = aval e s"
  apply (induction e)
  apply (simp_all split: aexp.split)
  by auto
 
text \<open>Ahora eliminamos todas las aplicaciones de 0 en sumas (x+0)\<close>

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N 0) x  = x " |
"plus (V x) = V "
"plus (Plus x y) =  "

lemma aval_plus[simp]

 
end