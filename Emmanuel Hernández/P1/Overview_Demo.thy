theory Overview_Demo
  imports Main
begin
(* Este es un comentario *)

text \<open> Esto es tambien 
un comentario compatible con \latex \<close>

text \<open> Esto es tambien 
un comentario compatible con \latex \<close>

term "True"
term "False"
term "true"
term "True & False"
term "True \<and> False"
value "True & False"
value "True & p"

(*Para desplegar tipos en jEdit: Ctrl+mouse*)

term "n + n = 0"
term "(n::nat) + n = 0"

(*Todos los terminos deben de ser correctos en tipo

term "True + False"
*)

text \<open>Inferencia de tipo\<close>

term "f (g x) y"
term "h (%x. f (g x))"
term "h (\<lambda>x. f (g x))"
term "%x. x+x"

(*Tipo incorrecto: 

term "\<lambda>x. x x"
*)

term "(1,2,3::nat)"

term "(\<and>)"
term "(\<or>)"
term "\<not>p"
term "(\<longrightarrow>)"
term "(\<longleftrightarrow>)"
term "Suc x"

end