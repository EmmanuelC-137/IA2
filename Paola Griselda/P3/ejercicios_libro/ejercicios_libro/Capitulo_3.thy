theory Capitulo_3
  imports Capitulo_3_AExp
begin

subsection \<open>EJERCICIOS CAPÍTULO 3\<close>

text \<open>********************************************************\<close>
text \<open>Ejercicio 3.1: Comprobar que asimp_const es óptima\<close>


fun optimal :: "aexp \<Rightarrow> bool"  where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus e1 e2) = (optimal e1 \<and> optimal e2)"

lemma optimal_asimp_const: "optimal (asimp_const a)"
  apply (induction a)
  apply (auto split: aexp.split)
  done


text \<open>***************************************************************\<close>
text \<open> Ejercicio 3.2: Optimización avanzada (Constant Folding)\<close>

(*1.Función que suma todas las constantes del árbol*)
fun sumN :: "aexp \<Rightarrow> int" where
"sumN (N n) = n" |
"sumN (V x) = 0" |
"sumN (Plus e1 e2) = sumN e1 + sumN e2"

(*2 Función que reemplaza todas las constantes por 0*)
fun zeroN :: "aexp \<Rightarrow> aexp" where
"zeroN (N n) = N 0" |
"zeroN (V x) = V x" |
"zeroN (Plus e1 e2) = Plus (zeroN e1) (zeroN e2)"

(*3.Función que separa: suma el árbol con 0 y el  total de constantes*)
definition sepN :: "aexp \<Rightarrow> aexp" where
"sepN t = Plus (zeroN t) (N (sumN t))"

(*Demostración de que la separación no altera el valor final*)
lemma aval_sepN: "aval (sepN t) s = aval t s"
  apply (simp add: sepN_def) (*Expandimos la definición de sepN*)
  apply (induction t)  (*inducción estructural sobre el árbol t*)
  apply (auto)  (*Auto resuelve la aritmética sin problemas*)
  done

(*4. Función final que elimina los 0 usando asimp*)
definition full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp t = asimp (sepN t)"

(*Demostración final de la optimización completa*)
lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
  apply (simp add: full_asimp_def aval_sepN) (*Simplificamos usando la definición y el lema anterior*)
  done

text \<open>*******************************************************************\<close>
text \<open> Ejercicio 3.3: Sustitución en expresiones aritméticas\<close>

(*1.Definición de la función de sustitución*)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if x = y then a else V y)" |
"subst x a (Plus e1 e2) = Plus (subst x a e1) (subst x a e2)"

(*2.Lema de sustitución*)
lemma subst_lemma[simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  apply (auto)
  done

(*3. Corolario: Sustituir expresiones equivalentes*)
lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (simp)
  done

text \<open>*******************************************************************\<close>
text \<open> Ejercicio 3.4: Extender aexp con Multiplicación, times\<close>

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(*1.Extendemos el tipo de dato con Times*)
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

(*2.Actualizamos la evaluación para soportar times*)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s" |
"aval (Times a b) s = aval a s * aval b s"

(*3 Función plus original, optimizando ceros en suma*)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i) (N j) = N (i + j)" |
"plus (N i) e = (if i = 0 then e else Plus (N i) e)" |
"plus e (N i) = (if i = 0 then e else Plus e (N i))" |
"plus e1 e2 = Plus e1 e2"

lemma aval_plus[simp]:
  "aval (plus e1 e2) s = aval e1 s + aval e2 s"
  apply (induction e1 e2 rule: plus.induct)
  apply (auto)
  done

(*4.Nueva Función times, optimizando 0 y 1 en multiplicación*)
fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"times (N i) (N j) = N (i * j)" |
"times (N i) e = (if i = 0 then N 0 else if i = 1 then e else Times (N i) e)" |
"times e (N i) = (if i = 0 then N 0 else if i = 1 then e else Times e (N i))" |
"times e1 e2 = Times e1 e2"

(*Demostración de que la nueva función times no altera la semántica*)
lemma aval_times[simp]:
  "aval (times e1 e2) s = aval e1 s * aval e2 s"
  apply (induction e1 e2 rule: times.induct)
  apply (auto)
  done

(*5.Actualizamos asimp para que use ambas funciones de optimización*)
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus e1 e2) = plus (asimp e1) (asimp e2)" |
"asimp (Times e1 e2) = times (asimp e1) (asimp e2)"

(*6.Teorema final de corrección de asimp*)
theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto)
  done

text \<open>*********************************************************************\<close>
text \<open>Ejercicio 3.5: Post-incremento y División (Side-effects)\<close>

(*1. Nuevo tipo de dato con Post-incremento (PcInc) y División (Div)*)
datatype aexp2 = 
    N int 
  | V vname 
  | Plus aexp2 aexp2 
  | Div aexp2 aexp2 
  | PcInc vname  (*Representa x++*)

(*2. Función de evaluación con propagación de estado y manejo de errores*)
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N n) s = Some (n, s)" |
"aval2 (V x) s = Some (s x, s)" |
"aval2 (PcInc x) s = Some (s x, s(x := s x + 1))" | (*Post-incremento: devuelve el valor actual (s x), pero el estado devuelto se actualiza sumando 1*)
(*Suma: evaluamos de izquierda a derecha pasando el estado modificado s*)
"aval2 (Plus a b) s = 
  (case aval2 a s of
     None \<Rightarrow> None |
     Some (v1, s') \<Rightarrow> 
       (case aval2 b s' of
          None \<Rightarrow> None |
          Some (v2, s'') \<Rightarrow> Some (v1 + v2, s'')))" |
(*División: Similar a la suma, pero agregamos una caso para evitar la división por 0*)
"aval2 (Div a b) s = 
  (case aval2 a s of
     None \<Rightarrow> None |
     Some (v1, s') \<Rightarrow> 
       (case aval2 b s' of
          None \<Rightarrow> None |
          Some (v2, s'') \<Rightarrow> if v2 = 0 then None else Some (v1 div v2, s'')))"

(*Pruebas rápidas para comprobar el funcionamiento*)

(*Prueba 1: División entre 0, debe dar None*)
value "aval2 (Div (N 10) (N 0)) <>"
(*Prueba 2: El post incremento devuelve 0, pero actualiza el estado internamente*)
value "aval2 (PcInc ''x'') <>"
(*Prueba 3: Secuencia de operaciones. x++ suma con x++
   El primer x++ devuelve 0 y cambia x a 1. 
   El segundo x++ lee ese 1, y cambia x a 2. 
   Total: 0 + 1 = 1, y el estado final de x es 2*)
value "aval2 (Plus (PcInc ''x'') (PcInc ''x'')) <>"

end