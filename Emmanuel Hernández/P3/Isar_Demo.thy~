theory Isar_Demo
  imports Complex_Main
begin

thm surj_def

lemma test:"\<not> surj(f::'a \<Rightarrow> 'a set)"
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" 
    by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<in> f x} = f a" 
    by blast
from 2 show "False" by blast

(*Esta mal el codigo, checar con la imagen*)

end