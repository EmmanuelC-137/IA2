theory examples
imports Main
begin

(*Demostracion de len :: "'a list \<Rightarrow> N" (ejercicio erroneo)*)

term "Suc"
 
datatype N = cero | suc N
 
thm N.inject
thm N.distinct
thm N.induct
 
fun suma:: "N\<Rightarrow>N\<Rightarrow>N" where
"suma cero y = y" |
"suma (suc x) y = suc (suma x y)"
 
fun len :: "'a list \<Rightarrow> N" where
"len Nil = cero" |
"len (Cons x xs) = suc (len xs)"
 
 
lemma len_app[simp]: "len (app xs ys) = suma (len xs) (len ys)"
  apply(induction xs)
   apply(auto)
  done
 
lemma suma_conm: "suma x y = suma y x"
  apply(induction x)
   apply(auto)
  done
 
lemma "len (rev xs) = len xs"
  apply(induction xs)
   apply(auto simp add: suma_conm)
  done
 
 
 
(*Definicion de funcion snoc *) 
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # snoc ys x"

(*Definicion de lemma con forme a la funcion snoc*)

  apply(induction rule: palindrome.induct)
    apply(auto)
  done

end