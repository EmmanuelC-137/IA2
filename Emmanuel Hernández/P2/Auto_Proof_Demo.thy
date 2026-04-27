theory Auto_Proof_Demo
imports Main
begin

section \<open>Lógica y Conjuntos\<close>

(* para toda "x" existe "y" *)
lemma "\<forall> x. \<exists> y. x = y"
  by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n"
  by fastforce

text \<open> Pruebas simples in FOL y teoría de conjuntos son automáticas
Ejemplo: si T es total, A es antisimetrica y T es subconjunto de A,
entonces A es subconjunto de T\<close>

lemma AT:
"\<lbrakk>\<forall>x y. T x y \<or> T y x;
\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
\<forall>x y. T x y \<longrightarrow> A x y \<rbrakk> \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
  by blast

lemma "R\<^sup>* \<subseteq> (R \<union> S)\<^sup>*"
  using rtrancl_Un_subset by auto


text \<open>Encuentra P e intenta sledgehammer\<close>

lemma "a#xs = ys @[a] \<Longrightarrow> set xs = set ys"
  sledgehammer
  by (metis append_butlast_last_id butlast.simps(2) butlast_snoc
      last.simps last_snoc rotate1.simps(2) set_rotate1)


text \<open>Aritmética\<close>

lemma"\<lbrakk> (a::int) \<le> f x + b; 2 * f x < c \<rbrakk> \<Longrightarrow> 
        2*a + 1 \<le> 2*b + c"
  by arith


lemma "\<forall> (k::nat) \<ge> 8. \<exists>i j. k = 3*i + 5*j"
  by arith


thm algebra_simps
lemma "(i+j)*(i-j) \<le> i*i + j*(j::int)"
  by (simp add: algebra_simps)

lemma "(5::int) ^ 2 = 20 + 5"
  by simp

thm exI
(* conjI  Asume que P es verdadero y Q tambien es verdadero; por tanto P y Q son verdaderos *)
thm conjI
thm conjI[of "a=b" "False"]

lemma "(\<exists>a b (c::nat). (a^2 + b^2 = c^2))"
  apply (rule_tac x="3" in exI)
  apply (rule_tac x="4" in exI)
  apply (rule_tac x="5" in exI)
  by auto

(* Rule: Unifica la conclusion de la regla, con la conclusion de la meta por probar.
Y se aplica de adelante hacia atras. *)

  (* Una meta variable no es mas que una variable que puede ser reprecenada con cualquier valor. 
  Estas se reconocen facilmente porque su estructura es ?P o ?Q en la consola*)
(* blast aplica las reglas automaticamente *)
end