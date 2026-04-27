theory Tree_Demo
  imports Main
begin

(* Solo se coloca comilla doble si tiene espacios
datatype 'a tree = Leaf | Node "'a tree" "'a" "'a tree" *)
datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

lemma "Leaf \<noteq> Node l x r"
  by auto

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Leaf = Leaf" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

value "mirror (Node (Node Leaf a Leaf) b t)"

thm tree.induct

lemma mirror_mirror[simp]: "mirror (mirror t) = t"
  apply (induction t)
   apply auto
  done

thm mirror_mirror

(* text <Ejemplo de una funcion que tiene más ecuaciones que contructores> *)

fun sep :: "'a => 'a list => 'a list" where
"sep x [] = []" |
"sep x [a] = [a]" |
"sep x (a # bs) = a # x # sep x bs"

thm sep.simps

thm sep.induct

value "sep x [1,2,3,4,5::nat]"

end