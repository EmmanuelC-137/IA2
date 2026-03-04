theory T1_AExp
  imports Main
begin

subsection \<open>Expresiones Aritmeticas\<close>

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(*Los strings en Isabelle se denotan por dos comillas simples*)
value " ''hola mundo'' "
(*Definición de la esructura de datos con la que vamos a representar las estructuras numericas*)
(*Sintacticamente los enteros son diferentes de las cadenas y de las expresiones*)
datatype aexp = N int | V vname | Plus aexp aexp

thm aexp.distinct
thm aexp.induct

(*Recibe un estado, función *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s "

value "aval (Plus(V ''x'') (N 5))
            (\<lambda>x. if x = ''x'' then 10 else 0)"

text \<open>El mismo estado pero usandno notación mas corta\<close>

value "aval (Plus(V ''x'') (N 5)) ((\<lambda>x. 0) (''x'' := 7))"

value "aval (Plus (V ''x'') (V ''y'')) (((\<lambda>x. 0)(''x'' := 7))(''y'' := 10))"


text \<open>De forma mas compacta\<close>

definition null_state ("<>") where
"null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds \<Rightarrow> 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <=  "_Update (_State b) bs"

thm refl (*axioma t es igual a t para todo t*)

(*en la repersentación interna del lado derecho al lado izq sintacticamente son iguales*)
lemma "<a:=1, b:=2> = (<> (a:=1)) (b:=2::int)"
  by (rule refl)

text \<open>esta, se obtiene un 5 poque no coinciden los strings \<close>
value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"
value "aval (Plus (V ''x'') (N 5)) < ''y'' := 7>"

text \<open>Martes 03 de Marzo\<close>

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus e1 e2) = 
  (case (asimp_const e1, asimp_const e2) of
  (N x, N y) \<Rightarrow> N (x + y) |
  (e1, e2) \<Rightarrow> Plus e1 e2)"

value "asimp_const (Plus (V ''x'') (Plus (N 5) (N 6)))"

theorem aval_asimp_const:
  "aval (asimp_const e) s = aval e s"
  apply (induction e)
  apply (simp_all split: aexp.split)
  by auto
 
text \<open>Ahora eliminamos todas las aplicaciones de 0 en sumas (x+0) --> x \<close>

(* Definición optimizada de la función plus*)

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N x) (N y) = N (x + y)" |  (*Suma de dos números*)
  "plus (N i) e = (if i = 0 then e else Plus (N i) e)" |  (* evalua si i es iual a 0, 0 + e = e*)
  "plus e (N i) = (if i = 0 then e else Plus e (N i))" |  (*lo mismo pero cuando el número esta del lado derecho  e + 0 = e*)
  "plus e1 e2 = Plus e1 e2" (*Caso general por ejemplo no son dos números fijos(constantes) y tampoco hay un cero*)

(*Demostración de que la semántica*)
lemma aval_plus[simp]:
  "aval (plus e1 e2) s = aval e1 s + aval e2 s"
  apply (induction e1 e2 rule: plus.induct)
  apply (auto)
  done
(*función que toma dos exp aritméticas y las suma,
 pero intentando simplificar el resultado si hay constantes o 0*)
fun plus_case :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus_case e1 e2 = 
    (case (e1, e2) of 
      (N x, N y) \<Rightarrow> N (x + y) |
      (N i, e) \<Rightarrow> (if i = 0 then e else Plus (N i) e) |
      (e, N i) \<Rightarrow> (if i = 0 then e else Plus e (N i)) |
      (x, y) \<Rightarrow> Plus x y)"

lemma aval_plus_case[simp]:
  "aval (plus_case e1 e2) s = aval e1 s + aval e2 s"
  apply (cases "(e1, e2)") (*Le decimos que divida la prueba evaluando el par*)
  apply (auto split: aexp.split) (*split ayuda a resolver los subcasos del case*)
  done

text \<open>Pruebas de la función plus\<close>
value "plus (N 5) (N 3)" (*Suma de dos constantes 5+3 debería sumarlos directamente*)
value "plus (V ''x'') (N 0)" (*Suma con 0 derecha x+0  ignora el 0 y devuelve solo la variable*)
value "plus (N 0) (V ''y'')" (*Suma con 0  izq 0+y ignora el 0 *)
value "plus (V ''x'') (N 5)" (*Caso general x+5, son dos constantes ni hay un 0 *)


end