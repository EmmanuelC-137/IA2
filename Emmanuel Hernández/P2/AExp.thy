theory AExp
  imports Main
begin

subsection \<open>Expresiones aritmeticas\<close>

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(*Los strings en Isabelle se denotan por dos comillas simples*)

value "''hola mundo''"

(*Defiición de la esructura de datos con la que vamos a representar las estructuras numericas*)
(*Sintacticamente los entyero son diferentes de las cadenas y de las expresiones*)
datatype aexp = N int | V vname | Plus aexp aexp

thm aexp.distinct
thm aexp.induct

(*Recibe un estado, función *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s "

value "aval (Plus (V ''x'') (N 5)) 
            (\<lambda>x. if x = ''x'' then 10 else 0)"

text \<open>El mismo estado (pero usando notación más corta).\<close>

value "aval (Plus (V ''x'') (N 5)) 
            ((\<lambda>x. 0) (''x'' := 7))"

value "aval (Plus (V ''x'') (V ''y'')) 
            (((\<lambda>x. 0) (''x'' := 7)) (''y'' := 10))"

text \<open>De forma más compacta.\<close>

definition null_state ("<>") where
"null_state \<equiv> (\<lambda>x. 0)"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma "<a:=1, b:=2> = (<> (a:=1)) (b:=2::int)"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) < ''x'' := 7>"

value "aval (Plus (V ''x'') (N 5)) < ''y'' := 7>"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus e1 e2) = 
  (case (asimp_const e1, asimp_const e2) of 
    (N x, N y) \<Rightarrow> N (x+y)
  | (e1, e2) \<Rightarrow> Plus e1 e2)"

value "asimp_const (Plus (V ''x'') (Plus (N 5) (N 6)))"

theorem aval_asimp_const:
  "aval (asimp_const e) s = aval e s"
  apply (induction e)
    apply (simp_all split: aexp.split)
  by auto


(* Toda propiedad recursiva se prueba por induccion*)


text \<open>Ahora eliminamos todas las apariciones de 0 en sumas (x + 0) --> x\<close>

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N n1) (N n2) = N (n1 + n2)" |
"plus (N n) e = (if n = 0 then e else Plus (N n) e)" |
"plus e (N n) = (if n = 0 then e else Plus e (N n))" |
"plus e1 e2 = Plus e1 e2"

lemma aval_plus[simp]:
  "aval (plus e1 e2) s = aval e1 s + aval e2 s"
  apply (induction e1 e2 rule: plus.induct)
  by auto

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus e1 e2) = plus (asimp e1) (asimp e2)"

value "asimp (Plus (Plus (N 0) (N 0)) 
                   (Plus (V ''x'') (N 0)))"

theorem aval_simp[simp]:
  "aval (asimp a) s = aval a s"
  apply (induction a) (*Induccion Estructural*)
  by auto


end