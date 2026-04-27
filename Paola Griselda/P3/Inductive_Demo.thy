imports Main

begin

Inductive_Demo.thy

text \<open>Definición\<close>

inductive

text \<open>Reglas de Introducción\<close>
thm ev0 evSS

thm ev.intros(*Regla de intoducc\<acute>\<acute>on por wuer introduce el simbolo ev en la conslición*)
thm ev.cases (*Regla de eliminación *)
thm ev.induct (*Regla de Inducción*)

text \<open>Uso de las reglas de introducción\<close>
lemma "ev (Suc(Suc(Suc(Suc 0))))" (*Comprobar que el 4 es par*)
  apply (rule evSS) (**)
  apply (rule evSS)
  apply (ev0 evSS) (*para 2*)
  done

thm evSS[OF evSS[OF ev0]] (*El teorema thm evSS tiene 1 metavariable en este caso n*)

text \<open>Definición recursiva de números pares\<close>

fun evn :: "nat \<Rightarrow> bool" where
"evn 0  = True" |
"evn (Suc 0) = False " |

aplicar el esquema computacional sobre la inducción ev 

end