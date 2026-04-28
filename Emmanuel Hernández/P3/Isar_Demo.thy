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

lemma "A \<subseteq> B"
proof
  fix a (*Fijamos el elemento "a"*)
  assume "a \<in> A"
  show "a \<in> B" sorry
qed

lemma "P"
proof (rule ccontr)
  assume "\<not> P"
  show "False" sorry
qed

end