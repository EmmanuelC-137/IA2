theory ASM imports BExp begin

subsection \<open>Máquina con pila\<close>

datatype instr = LOADI val | LOAD vname | ADD

(* LOADI: pone el valor en el tope de la pila y mueve el tope
LOAD: toma el valor de una variable y pone en el tope de la pila
ADD: toma los dos ultimos valores del tope y el valor lo pone en el tope de la pila y borra los dos numeros sumados previamente.*)

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD x) s stk= s x # stk" |
"exec1 ADD _ (i#j#stk) = (i + j) # stk"

fun exec :: "instr list => state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

value "exec [LOADI 5, LOAD ''y'', ADD]
            <''x'' := 42, ''y'' := 43>
            [50]"

subsubsection \<open>Copilación\<close>

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

lemma exec_append[simp]: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  by (induction is1 arbitrary: is2 s stk, auto)

lemma exec_comp_g: "exec (comp a) s stk = aval a s # stk"
  by (induction a arbitrary: s stk, auto)

theorem exec_comp: "exec (comp a) s [] = [aval a s]"
  by (simp add: exec_comp_g)


end