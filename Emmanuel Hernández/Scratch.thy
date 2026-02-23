theory Scratch
  imports Main
begin

datatype N = cero | suc N

fun suma :: "N \<Rightarrow> N \<Rightarrow> N" where
"suma cero y = y" |
"suma (suc x) y = suc (suma x y)"

value "suma (suc (suc cero)) (suc (suc cero))"

fun mult :: "N \<Rightarrow> N \<Rightarrow> N" where
"mult cero y = cero" |
"mult (suc x) y = suma y (mult x y)"

lemma "mult (suma x y) z = suma (mult x y) (mult y z)"

proof -
  have assoc: "\<And>x y z. suma x (suma y z) = suma (suma x y) z" 
    by (induct_tac x, auto)

  show ?thesis
    apply (induction x, auto simp add: assoc) done
qed

end