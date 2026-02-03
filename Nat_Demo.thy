theory Nat_Demo
imports Main
begin

term "Suc"

datatype N = cero | suc N

thm N.inject
thm N.distinct
thm N.induct

fun suma:: "N\<Rightarrow>N\<Rightarrow>N" where
"suma cero y = y" |
"suma (suc x) y = suc (suma x y)"

thm suma.simps
thm suma.induct

lemma "suma y cero = y"
  apply (induction y)
   apply (auto)
  done

lemma "suma x (suc y) = suc(suma x y)"
  apply (induction x)
  by auto


end