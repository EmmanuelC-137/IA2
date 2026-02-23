theory Scratch
  imports Main
begin 

datatype N = cero | suc N  (*se definene los dos constructores *)

(*definir recursivamente sobre el primer argumento*)
fun suma :: "N \<Rightarrow> N \<Rightarrow> N" where
"suma  cero y = y" |
"suma (suc x) y = suc (suma x y)"

value "suma (suc (suc cero)) (suc (suc cero))"

fun mult :: "N \<Rightarrow> N \<Rightarrow> N" where
"mult cero y = cero" |
"mult (suc x) y = suma y (mult x y)"

(*Herramientas para encontrar contra ejemplos quickchech y nitpick, si hay contrajemplos
ya no hay necedidad de realizar la demostración ya que no va a ser posible*)

lemma "mult (suma x y) z = suma (mult x z)"
proof -
  have assoc: "\<And>x y z. suma x (suma y z) = suma (suma x y) z"
    by (induct_tac x, auto) (*puede apicar en las variables cuantificada, variables verdess*)
  show ?thesis 
  apply (induction x, auto simp add: assoc) (*no es suficiente, es decir, que se necesit aun lema para 
    probar la conjetura, induction sobre variables azules *)
  qed

end


