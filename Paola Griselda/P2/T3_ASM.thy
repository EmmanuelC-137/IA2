theory T3_ASM 
  imports T2_BExp begin

(*Carga valores de entero, carga el valor de una variable, instrucción ADD*)
(*Carga un valor en el tope de la pila, un valor en el tope de la pila, toma los ultimos dos
 valores del tope de la pila*)
subsection \<open>Máquina con pila\<close>

datatype instr = LOADI val | LOAD vname | ADD

(*Vamos a modelar el diseño de la pila con una lista*)
(*escupe una pila resultante*)
type_synonym stack = "val list"

(*Función que ejecuta una sola instrucción*)
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n)_ stk = n # stk" |
"exec1 (LOAD x) s stk = (s x) # stk" |
"exec1 ADD _ (i#j#stk) = (i+j) # stk"

(*Cuando la lista no tenemos elementos en la pila y cuandos solo 
se tiene un solo elemento*)
(*como programar la fun exec1 utilizando el tipo option*)

(*Fun que ejecuta un conjunto de instrucciones*)
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

value "exec [LOAD 5, LOAD ''y'', ADD]
      <''x'' := 42, ''y'' := 43>
      [50]"
subsection \<open>Compilación\<close>

(*oma una exp arimteica y vamos a generar una lista de instrucciónes
 y esas sintrsucciones ejecutan la expresión aritmetica *)
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]" 

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

(*Ejecuta una lista concatenada a otra*)
lemma exec_append[simp]: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  by (induction is1 arbitrary: is2 s stk, auto)


theorem exec_comp: "exec (comp a) s [] = [aval a s]"
  quickcheck, nitpick

(*Ejecuta una lista concatenada a otra*)
lemma exec_append[simp]:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply (induction is1 arbitrary: stk)
  apply (auto)
  done
(*
demostrar
en el libro marca como probrarlo
*)
(*Ejecuta una lista concatenada a otra*)
lemma exec_append[simp]:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply (induction is1 arbitrary: stk)
  apply (auto)
  done

lemma comp: "exec (comp a) s stk = aval a s # stk"
  apply (induction a arbitrary: stk) (*Si no se pone arbitary isabelle asume que la pila stk es fija e inmutable durante toda la prueba, debe funcionar para cualquier pila en cualquier momento*)
  apply (auto)
  done






