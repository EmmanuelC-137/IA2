theory Isar_Demo
  imports Complex_Main
begin

thm surj_def

lemma "\<not> surj(f::'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a"
    by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a"
    by blast
  from 2 show "False"
    by blast
qed

  
lemma "\<not> surj(f::'a \<Rightarrow> 'a set)"
proof  (*de 0 brincamos a 2 sin pasar por 1*)
  assume 0: "surj f"
  from 0 have 1: "\<exists>a. {x. x \<notin> f x} = f a"(*Se pueden poner etiquetas para cada submeta *)
    by (auto simp: surj_def)
  from 1 show "False" 
    by blast
qed

text \<open>No es  necesario el uso de etiquetas\<close>
(*La utima formula que se referenció con esa*)
lemma "\<not>surj(f::'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  from this show "False"
    by blast
qed

text\<open>"then" = "from this"\<close>
(**)
lemma "\<not>surj(f::'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  then show "False" 
    by blast
qed


text\<open>"hence" = "then have", "thus" = "then show"\<close>
lemma "\<not>surj(f::'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  thus "False"
    by blast
qed

text \<open>Enunciados etructurados: "fixes", "assumes", "shows"\<close>

lemma (*Demosrtración alternativa*)
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof - 
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by (auto simp: surj_def)
  thus "False" 
    by blast
qed

section \<open>Patrones de prueba\<close>

lemma "P \<longleftrightarrow> Q"(*Cuando se quiere demostrar cuando dos fun son iguales *)
proof 
  assume "P"
  show "Q" sorry
next
  assume "Q"
  show "P" sorry
qed

lemma "A = (B::'a set)" (*Que 2 conjuntos son iguales*)
proof 
  show "A \<subseteq> B" sorry
next
  show "B \<subseteq> A" sorry
qed

lemma "A \<subseteq> B" (*Probar algun conjunto de A es un subconjunto de B*)
proof 
  fix a(*fijar un elemento a esta dentro del conjunto A, asumiendo *)
  assume "a \<in> A"
  show "a \<in> B" sorry
qed


text \<open>Contradicción\<close>

thm ccontr

lemma "P"
proof (rule ccontr)
  assume " \<not>P"
  show "False" sorry
qed

text \<open>Distinción de casos\<close>

thm disjE (*regla de la eliminación de la disyunción*)

lemma "R" (*Se quiere demostrar R*)
proof cases (*Se  necesita cases para demostrar por casos*)
  assume "P" (*asummos P y bajo esa suposición*)
  show "R" sorry (*demostramos R*)
next
  assume "\<not>P"
  show "R" sorry
qed

lemma "R"
proof - (*colcamos - para que no se apique ninguna regla de introducción*)
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

thm exI (*regla de la introducción de la exixtencial*)
(* el x es una metavariable entonces puedeser sustituida por lo que se quiera *)

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a"
    by (auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" (*Todo el ejemplo circula en usar obtain y quietar el cuantificador exitencial *)
    by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a"
    by blast
  thus "False" 
    by blast
qed

lemma
  assumes "\<exists>x. \<forall>y. P x y"
    shows "\<forall>y. \<exists>x. P x y"
      proof
        fix y
        






end

