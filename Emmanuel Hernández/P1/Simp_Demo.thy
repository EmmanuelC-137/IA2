theory Simp_Demo
    imports Main
begin

section \<open>Como simplificar\<close>

text \<open>Sin suposiciones\<close>

lemma "ys @ [] = []"
  apply (simp)
  oops (*no se puede probar*)

text \<open>Simplificacion en suposiciones\<close>

lemma "[[xs @ zs = ys @ xs]; []@xs = []@[]]] \<Longrightarrow> ys = zs"
    apply (simp)
    done

thm algebra_simps

text \<open>Usando reglas adicionales\<close>
lemma "(a+b) * (a-b) = a*a - b*(b::int)"
  apply (simp add: algebra_simps)
  done

text \<open>Agregamos el atributo simp\<close>
declare algebra_simps[simp]

subsection \<open>Reescribir con definiciones\<close>

definition sq::"nat \<Rightarrow> nat" where
"sq n = n*n"

lemma "sq (n*n) = sq(n) * sq(n)"
  apply (simp add: sq_def)
  done

subsection \<open>Reescribir con reglas de induccion computacional\<close>
text \<open>Automatico\<close>

lemma "(A \<and> B ) = (if A them B else False)"
  apply (simp)
  done

text \<open>A mano (para Case)\<close>
thm list.split

lemma "1 <= (case ns of [] => 1 | n # _ => Suc n)"
    apply (simp split: list.split)
    done

subsection \<open>Aritmetics\<close>

text \<open>Aritmetica lineal\<close>

lemma "[[ (x::nat) <= y+z; z+x < y ]] => x < y"
  apply (simp add: algebra_simps)
  done

subsection \<open>Depuracion\<close>

lemma "rev [x] = []"
  using [[simp_trace]] apply simp
  oops


end