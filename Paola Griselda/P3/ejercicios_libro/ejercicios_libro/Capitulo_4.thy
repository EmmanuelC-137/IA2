theory Capitulo_4
  imports Main
begin

subsection \<open>EJERCICIOS CAPÍTULO 4\<close>

text \<open>*******************************************************************\<close>
text \<open>Ejercicio 4.1: Árboles Binarios de Búsqueda\<close>

(*1.Definición del tipo de dato árbol*)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(*2.Función que extrae todos los elementos del árbol como un conjunto, set*)
fun set_tree :: "'a tree \<Rightarrow> 'a set" where
"set_tree Tip = {}" |
"set_tree (Node l a r) = set_tree l \<union> {a} \<union> set_tree r"

(*Función que verifica si el árbol está ordenado*)
(*Se utilizan cuantificadores universales \<forall> *)
fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l i r) = ((\<forall>x \<in> set_tree l. x < i) \<and> 
                     (\<forall>x  \<in> set_tree r. i < x) \<and> 
                     ord l \<and> ord r)"

(*4. Función de inserción que mantiene el orden*)
fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
(*Si ya existe, se devuelve el mismo árbol*)
"ins x (Node l a r) = 
  (if x = a then Node l a r    
   else if x < a then Node (ins x l) a r 
   else Node l a (ins x r))"

(*5.Lema que insertar un elemento actualiza correctamente el conjunto de valores*)
lemma set_ins[simp]: "set_tree (ins x t) = {x} \<union> set_tree t"
  apply (induction t)
  apply (auto)
  done

(*6.Teorema principal: Insertar en un árbol ordenado preserva el orden*)
theorem ord_ins: "ord t \<Longrightarrow> ord (ins i t)"
  apply (induction t)
  apply (auto) (*auto usa internamente set_ins gracias a la etiqueta simp*)
  done

text \<open>**************************************************************\<close>
text \<open> Ejercicio 4.2: Palíndromos (Predicados Inductivos)\<close>

(*Definición del predicado inductivo con sus 3 reglas base*)
inductive palindrome :: "'a list \<Rightarrow> bool" where
pal_empty:  "palindrome []" |
pal_single: "palindrome [x]" |
pal_step:   "palindrome xs \<Longrightarrow>  palindrome (a # xs @ [a])"

(*Demostración, todo palíndromo es igual a su reverso*)
lemma "palindrome xs \<Longrightarrow>  rev xs = xs"
  apply (induction rule: palindrome.induct) (*Inducción sobre las reglas*)
  apply (auto)
  done

text \<open>******************************************************************\<close>
text \<open> Ejercicio 4.3: Clausura reflexiva y transitiva (star vs star')\<close>

(* definición estándar de star*)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

(*1. Definición alternativa: añadiendo pasos por el final (derecha)*)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

(*Dirección 1: star' implica star*)

(*Lema auxiliar 1: Enseñamos a star a dar un paso por la derecha*)
lemma star_append: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
  apply (auto intro: star.refl star.step)
  done

(*Demostración principal 1*)
lemma star'_imp_star: "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  apply (auto intro: star.refl star_append) (*Usamos nuestro lema auxiliar*)
  done

(*Dirección 2: star implica star'*)
(*Lema auxiliar 2: Enseñamos a 'star'' a dar un paso por la izquierda*)
(* Para que la inducción funcione, el predicado inductivo (star') debe ser la primera premisa*)
lemma star'_prepend: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
  apply (auto intro: star'.refl' star'.step')
  done

(*Demostración principal 2*)
lemma star_imp_star': "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  apply (auto intro: star'.refl' star'_prepend) (*Usamos el lema con la premisa invertida*)
  done

end