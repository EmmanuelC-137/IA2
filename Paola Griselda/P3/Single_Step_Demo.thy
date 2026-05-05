theory Single_Step_Demo
  imports Main
begin
(*teorema de la introducción de conjunción*)
thm conjI[of "hola mundo" "a todos"]

(*Lo que tienes en el lado izq en la ecu por ejemplo A=A*)
thm refl

(*aplicaión de conjI, la aplicacción hacia adelante*)
thm conjI
thm conjI[OF refl[of "a"]] (*el OF es como el moduspons*)

text \<open>el comando "thm" despliega 1 o mas teoremas\<close>
thm conjI impI iffI notI ccontr mp

text \<open>Intanciación de toremas: "of"\<close>
thm conjI[of "A" "B"]
thm conjI[of "A"]
thm conjI[of _ "B"] 

text \<open>"OF"\<close>
thm refl[of "a"]
thm conjI conjI[OF refl[of "a"] refl[of "b"]] (*Con el OF aplicamos una regla de inferencia de atras hacia adelante*)
thm conjI[OF refl[of "a"]] (*por partes*)
thm conjI[OF _ refl[of "b"]]


text \<open>Una demostración de adelante a atras\<close>
lemma "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> A \<and> B"
  apply (rule conjI)
  apply assumption (*aplicamos la 1 submeta por probar*)
  apply assumption (*aplicamos la 2 submeta por probar*)
  done

lemma "\<lbrakk>P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> P \<longrightarrow> Q"
  apply (rule impI)
  apply (assumption)
  done

lemma "\<lbrakk>P \<longrightarrow> Q; Q \<longrightarrow> R\<rbrakk> \<Longrightarrow> P \<longrightarrow> R"
  apply (rule impI)
  apply (erule mp)
  apply (erule mp)
  apply (assumption)
  done 