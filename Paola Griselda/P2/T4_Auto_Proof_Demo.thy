theory T4_Auto_Proof_Demo
  imports Main
begin

section \<open>Lógica y conjuntos\<close> 

(*Lema: cuantificador universal all, cuantificador existencial*)
 (*Para toda x exixte una y tal que x es igual a y*)
(*auto demuestra de forma automatica, ya que se demuestra con argumentos lógicos*)
lemma "ALL x. EX y. x = y" 
  by auto

(*Razonamiento de cojuntos aplicando auto*)
lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<inter> C"
  by auto

(*A existe una lista ys tal que xs es ys concatenado con ys, asume que la lstya us esta dento
del conjunto A, bajo esas dos suopociciones hacen que exixta un n tal que la longitud de la
lista us es igual a n+n*)
lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow>
        \<exists>n. length us = n+n"
  by fastforce

text \<open>Pruebas simples in FOL y teoría de conjuntos son automáticas
Ejemplo: Si T es total, A es antisimetrica y T es subconjunto de A, entonces
A es subconjunto de T\<close>
lemma AT: 
  "\<lbrakk>\<forall>x y. T x y \<or> T y x;
    \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
   \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
  \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
  by blast

(*cerradura transitiva es el *, la cerradura de R es *)
lemma "R\<^sup>* \<subseteq> (R \<union> S)\<^sup>*"
  using rtrancl_Un_subset by auto

text \<open>Encuentre P e intenta sledgehammer\<close>(*Sustituir P tal que el lemma sea verdadero*)
(*lemma "a#xs = ys @ [a] \<Longrightarrow> P"*)

(*las listas xs y ys tengan la misma longitud *)
(*lemma "a#xs = ys @ [a] \<Longrightarrow> length xs = length ys"*)

(*Los onjuntos formados por los elemenos de la lista sean el mismo conjunto*)
lemma "a#xs = ys @ [a] \<Longrightarrow> set xs = set ys"
  sledgehammer

  text\<open>Aritmética\<close>

lemma "\<lbrakk> (a::int) \<le> f x + b; 2 * f x < c \<rbrakk> \<Longrightarrow>
  2*a + 1 2*b + c"
  by arith

lemma "\<forall> (k::nat) \<ge> 8. \<exists>i j. k = 3*i + 5*j"
  by arith

thm algebra_simps

lemma "(i+j)*(i-j) \<le> i*i + j*(j::int)"
  by (simp add: algebra_simps)

lemma "(5::int) ^ 2 = 20 + 5"
  by simp

(*reglas de inferencia *)
thm exI
thm conjI
thm conjI[of "a=b" "False"] (*es necesario asignar "a=b" valor con el tipo correcto*)

(*queremos encontrar un *)
lemma "(\<exists>a b (c::int).( a^2 + b^2 = c^2))"
  apply(rule_tac x="3" in exI) (*Aplica el método rule_tac y 3 se instancia en "a" utilizando la regla exI *)
  apply(rule_tac x="4" in exI) (*4 se instancia en "b" *)
  apply(rule_tac x="5" in exI) (*5 se instancia en "b" *)
  by simp (*by auto*)



end