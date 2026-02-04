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

end