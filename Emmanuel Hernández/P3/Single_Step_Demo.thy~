theory Single_Step_Demo
imports Main
begin

thm conjI[of "Hola mundo"]
thm conjI[of "5 = 6"]

(* Pruebas hacia adelante con OF*)

(* ?t = ?t: el valor que se establese es el mimso el lado derecho e izquierdo *)
thm refl

thm conjI
thm conjI[OF refl [of "a"]]

text \<open> El comando "thm" despliega uno o más teoremas \<close>
thm conjI impI iffI notI ccontr mp

text \<open> Instanciación de teoremas: "of"\<close>
thm conjI[of "A" "B"]
thm conjI[of "A"]
thm conjI[of _ "B"]

text \<open> Intanciaciones por nombre \<close>
thm conjI[where ?Q = "B"]

text \<open>"OF"\<close>
(* OF es una regla de inferencia de atras hacia adelante, es decir que algo
de tipo !P \<Rightarrow> ?Q ?P  
              -----
                ?Q      

aplica una aplicaicion de una regla y aplica modusponens.

A diferencia de el of en minusculas el cual solo lo hace en 
una meta variable
 *)
thm refl[of "a"]
thm conjI conjI[OF refl[of "a"] refl[of "b"]]
thm conjI[OF refl[of "a"]]
thm conjI[OF _ refl[of "b"]]

thm conjI
(* conjI: ?P \<Rightarrow> ?Q \<Rightarrow> ?P\<and>?Q *)
text \<open>Una demostración de adelante a atras\<close>
lemma "\<lbrakk>A;B\<rbrakk> \<Longrightarrow> A \<and> B "
  apply (rule conjI)
   apply assumption
  apply assumption
  done

(*
El truco es ver el simbolo de la conclusion
  \<longrightarrow>   (implicación)
   \<and>
  / \
 P   Q
Siempre que se necesita demostrar algo, simpre se debe de aplicar la regla
de introduccion segun el tope de la conclusion, en este caso es la implicacion, en el anterior
fue la conjunción.

*)
lemma "\<lbrakk>P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> P \<longrightarrow> Q"
  apply (rule impI)
(*Recuerda usar siempre el quickcheck para ver si hay contraejemplos*)
(*Recuerda usar tambien el sledgehammer*)
  apply assumption
  done


lemma "\<lbrakk>P \<longrightarrow> Q; Q \<longrightarrow> R\<rbrakk> \<Longrightarrow> P \<longrightarrow> R"
  apply(rule impI)
(*En caso de fallas "assumption" se debe de manipular*)
  apply (erule mp)
  apply (erule mp)
  apply(assumption)
  done
end