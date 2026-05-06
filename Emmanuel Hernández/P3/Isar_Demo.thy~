theory Isar_Demo
  imports Complex_Main
begin

thm surj_def

lemma test:"\<not>surj(f::'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" 
    by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<in> f x} = f a" 
    by blast
  from 2 show "False"
    by blast
qed

lemma "\<not> surj (f:: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  from 1 show "False" by blast
qed

text \<open>No es necesario el uso de etiquetas\<close>
lemma "\<not>surj (f:: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  from this show "False" by blast
qed


text \<open>"then" = "from this"\<close>
lemma "\<not>surj (f:: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  then show "False" by blast
qed

text \<open>"hance" = "then have", "thus" = "then show"\<close>
lemma "\<not>surj (f:: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  thus "False" by blast
qed

text\<open>Enunciados estructurados: "fixes", "assumes", "shows"\<close>

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"

  proof -
    have "\<exists> a. {x. x \<notin> f x} = f a" using s
      by (auto simp: surj_def)
    thus "False" by blast
  qed

section \<open>Patrones de prueba\<close>
lemma "P \<longleftrightarrow> Q"
proof
  assume "P"
  show "Q" sorry
next
  assume "Q"
  show "P" sorry
qed

lemma "A = (B :: 'a set)"
proof
  show "A \<subseteq> B" sorry
next
  show "B \<subseteq> A" sorry
qed


lemma "A \<subseteq> B"
proof
  fix a (*Fijamos el elemento "a"*)
  assume "a \<in> A"
  show "a \<in> B" sorry
qed

text\<open>Contradiccion\<close>

thm ccontr (*Regla para demostrar por contradicción*)

lemma "P"
proof (rule ccontr)
  assume "\<not> P"
  show "False" sorry
qed

text\<open>Distinción de casos\<close>

thm disjE (*Regla de eliminacion: Elimina la disyuncion*)

lemma "R"
proof cases (*Regla para demostrar por casos*)
  assume "P"
  show "R" sorry
next
  assume "\<not>P"
  show "R" sorry
qed

lemma "R"
proof -
  have "P \<or> Q" sorry
  then show "R"
  proof
    assume "P"
    show "R" sorry
  next
    assume "Q"
    show "R" sorry
  qed
qed

thm exI (*Regla de introduccion de un existencial 
?P ?x \<Longrightarrow> \<exists>x. ?P x: Si P se cumple para x, entonces existe una x para  cada P*)

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" 
    by (auto simp: surj_def)
      (*Para quitar un cuantificador existencial, se usa el obtain*)
  then obtain a where " {x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a"
    by blast
  thus "False" by blast
qed

lemma assumes h1: "\<exists>x. \<forall>y. P x y" shows "\<forall>yy. \<exists>x. P x y"
proof
  have "\<exists>a. P a y"
    using h1 by blast
  then show "\<exists>x. P x y"
    by blast
qed

text \<open>Cadena de ecuaciones y desigualdades\<close>
lemma "(0::real) \<le> x^2 + y^2 - 2*x*y"
proof -
  have "0 \<le> (x-y)^2" by simp
  also have "... = x^2 + y^2 - 2*x*y"
    by (simp add: numeral_eq_Suc algebra_simps)
  finally show "0 \<le> x^2 + y^2 - 2*x*y" .
qed


section \<open>Unificación de patrones y meta variables \<close>
lemma "\<exists>xs. length xs = 0" (is "\<exists>xs. ?P xs")
proof
  show "?P([])" by simp
qed


lemma "\<exists>x y::int. x < z & z < y" (is "\<exists>x y. ?P x y")
proof -
  have "?P (z - 1) (z + 1)" by arith
  thus ?thesis by blast
qed


lemma assumes "x < (0::int)" shows "x * x>0"
proof -
  from `x<0` show ?thesis by (metis mult_neg_neg)
qed

lemma "\<exists>ys zs. xs = ys@zs \<and>
  (length ys = length zs \<or> length ys = length zs + 1)"
proof

qed



end