theory Tree_Demo
  imports Main
begin

(* Solo se coloca comilla doble si tiene espacios
datatype 'a tree = Leaf | Node "'a tree" "'a" "'a tree" *)
datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

lemma "Leaf \<noteq> Node l x r"
  by auto

end