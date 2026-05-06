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
  proof (*Al no especificar ninguna regla, Isabelle aplica automáticamente la regla estándar*)
    fix y (*Fijamos un elemento arbitrario y*)
    from assms obtain x where "\<forall>y. P x y" (*Utilizamos nuestra suposición inicial (assms) que afirma que existe un x que cumple la propiedad para todos los elementos. La palabra clave obtain nos permite extraer ese elemento específico y llamarlo x*)
      by blast
    hence "P x y" (*P x y es verdadero para cualquier y, entonces lógicamente también tiene que ser verdadero para nuestro y arbitrario que fijamos*)
      by blast
    thus "\<exists>x. P x y" (*P x y se cumple para este x y este y en particular, podemos concluir que existe algún elemento (nuestro x) que hace que P sea verdadero para y*)
      by blast


text \<open>Cadenas de ecuaciones y desigualdades\<close>

lemma "(0::real) \<le> x^2 + y^2 - 2*x*y"
proof -
  have "0 \<le> (x-y)^2" by simp
  also have "... = x^2+y^2-2*x*y" (*se usa (...) para la ultima fórmula*)
    by (simp add: numeral_eq_Suc algebra_simps)
  finally show "0 \<le> x^2 + y^2 - 2*x*y" .
qed

section \<open>Unificación de patrones y meta variables\<close>

lemma "\<exists>xs. length xs = 0" (is "\<exists>xs. ?P xs" (*probar la lista *)
proof 
  show "?P([])" by simp
qed

lemma "\<exists>x y::int. x < z & z < y" (is "\<exists>x y. ?P x y")
proof -
  have "?P (z-1) (z+1)" by arith
  thus ?thesis by blast

(*ejemplo de una suposición de que x < 0*)
(*si la suposición, la formula es grande se le coloca nombre*)
(*lemma assumes a_menor_cero:"x < (0::int)" shows "x*x>0*)
lemma assumes "x < (0::int)" shows "x*x>0"
proof - 
  from `x<0` show ?thesis by (metis mult_neg_neg)
qed
(*
lemma "\<exists>ys zs. xs = ys@zs" \<and> 
(length ys = length zs \<or> length ys = length zs + 1)"
sorry
*)


lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  let ?m = "(length xs + 1) div 2"  (*Define una metavariable llamada ?m que representa el punto donde vamos a cortar la lista, El truco matemático: Al sumar 1 antes de dividir entre 2, se logra un "redondeo hacia arriba" para enteros, Si la longitud es 4 (par): (4 + 1) div 2 = 2.Si la longitud es 5 (impar): (5 + 1) div 2 = 3.*)
  (*Construimos ys tomando los primeros ?m elementos de la lista original (take).
  Construimos zs tomando el resto, es decir, eliminando los primeros ?m elementos (drop).*)
  define ys where "ys = take ?m xs"
  define zs where "zs = drop ?m xs"

  have "xs = ys @ zs" by (simp add: ys_def zs_def) (*concatenación*)
  hence "xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)" (*e pides que demuestre la condición completa del lema. Como ya demostraste la primera mitad en el paso anterior*)
    by (auto simp add: ys_def zs_def)
  thus ?thesis by blast
qed

end

