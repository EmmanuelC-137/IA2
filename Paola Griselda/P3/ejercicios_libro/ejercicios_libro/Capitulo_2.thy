theory Capitulo_2
  imports Main
begin

subsection \<open>EJERCICIOS CAPÍTULO 2\<close>

text \<open> Ejercicio 2.1: Evaluar expresiones con el comando value\<close>

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"
value "[a,b] @ [c,d]"

text \<open>**********************************************************\<close>
text \<open> Ejercicio 2.2: Función add, asociatividad, conmutatividad y double\<close>

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)" 

lemma add_assoc: "add (add m n) p = add m (add n p)" 
  apply (induction m)
  apply (auto)
  done

(*1.Lema auxiliar: Sumar 0 por la derecha*)
lemma add_0_right [simp]: "add m 0 = m"
  apply (induction m)
  apply (auto)
  done

(*2. Lema auxiliar: Sumar el sucesor por la derecha*)
lemma add_Suc_right [simp]: "add m (Suc n) = Suc (add m n)"
  apply (induction m)
  apply (auto)
  done

text \<open> Lema principal: Conmutatividad\<close>
lemma add_comm: "add m n = add n m"
  apply (induction m)
  apply (auto)
  done

text \<open>*****************************************************************\<close>
text \<open>Ejercicio 2.3: Contar ocurrencias de un elemento\<close>

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] y = 0" |
"count (x#xs) y = (if x = y then Suc (count xs y) else count xs y)"

theorem count_le_length: "count xs x \<le> length xs"
  apply (induction xs)
  apply (auto)
  done


text \<open>****************************************************************\<close>
text \<open> Ejercicio 2.4: Funciones snoc y reverse sin usar append o rev \<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] y = [y]" |
"snoc (x#xs) y = x # (snoc xs y)" 

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x#xs) = snoc (reverse xs) x" 

(*Lema auxiliar cómo interactúa reverse con snoc*)
lemma reverse_snoc[simp]: "reverse (snoc xs a) = a # reverse xs"
  apply (induction xs)
  apply (auto)
  done

theorem reverse_reverse: "reverse (reverse xs) = xs"
  apply (induction xs)
  apply (auto)
  done

text \<open>******************************************************\<close>
text \<open> Ejercicio 2.5: Fórmula de suma de Gauss\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = Suc n + sum_upto n" 

lemma sum_upto_formula: "sum_upto n = n * (n + 1) div 2" 
  apply (induction n)
  apply (auto)
  done

text \<open>*********************************************************\<close>
text \<open> Ejercicio 2.6: Árboles y recolección de elementos\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree" 

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = contents l @ [a] @ contents r" 

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = sum_tree l + a + sum_tree r" 

lemma sum_tree_contents: "sum_tree t = sum_list (contents t)" 
  apply (induction t)
  apply (auto)
  done

text \<open>*************************************************************\<close>
text \<open> Ejercicio 2.7: Árboles con valores en las hojas\<close>

datatype 'a tree2 = Tip "'a" | Node "'a tree2" 'a "'a tree2" 

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Tip a) = Tip a" |
"mirror2 (Node l a r) = Node (mirror2 r) a (mirror2 l)" 

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip a) = [a]" |
"pre_order (Node l a r) = a # (pre_order l @ pre_order r)" 

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip a) = [a]" |
"post_order (Node l a r) = post_order l @ post_order r @ [a]"

lemma pre_order_mirror: "pre_order (mirror2 t) = rev (post_order t)" 
  apply (induction t)
  apply (auto)
  done

text \<open>*****************************************************************\<close>
text \<open> Ejercicio 2.8: Función intersperse \<close>


fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x#y#xs) = x # a # intersperse a (y#xs)" 

lemma intersperse_map: "map f (intersperse a xs) = intersperse (f a) (map f xs)" 
  apply (induction xs rule: intersperse.induct)
  apply (auto)
  done

text \<open>*********************************************************\<close>
text \<open> Ejercicio 2.9: Suma recursiva de tail-recursive\<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

(*Lema auxiliar, comportamiento de itadd con respecto a Suc en el segundo argumento*)
lemma itadd_Suc_right: "itadd m (Suc n) = Suc (itadd m n)"
  apply (induction m arbitrary: n)
  apply (auto)
  done

(*Lema principal*)
lemma itadd_is_add: "itadd m n = add m n"
  apply (induction m arbitrary: n)
  apply (auto simp add: itadd_Suc_right)
  done

text \<open>**********************************************************************************\<close>
text \<open> Ejercicio 2.10: Árboles sin información (esqueletos) y explode \<close>

datatype tree0 = Tip0 | Node0 tree0 tree0 

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip0 = 1" |
"nodes (Node0 l r) = 1 + nodes l + nodes r" 

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node0 t t)"

(*Ecuación solicitada, cada vez que explotamos, duplicamos el árbol anterior e insertamos un nodo raíz
 El tamaño sigue la fórmula: nodes (explode n t) = 2^n * nodes t + 2^n - 1*)
lemma explode_size: "nodes (explode n t) = (2^n) * nodes t + (2^n) - 1"
  apply (induction n arbitrary: t)
  apply (auto simp add: algebra_simps) 
  done

text \<open>*************************************************************\<close>
text \<open> Ejercicio 2.11: Expresiones polinómicas y evaluación \<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp 

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const c) x = c" |
"eval (Add e1 e2) x = eval e1 x + eval e2 x" |
"eval (Mult e1 e2) x = eval e1 x * eval e2 x" 

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (c#cs) x = c + x * evalp cs x" 

(*Funciones auxiliares para sumar y multiplicar polinomios representados como listas*)
fun addp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"addp [] ys = ys" |
"addp xs [] = xs" |
"addp (x#xs) (y#ys) = (x+y) # addp xs ys"

fun multp_const :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"multp_const c [] = []" |
"multp_const c (x#xs) = (c*x) # multp_const c xs"

fun multp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"multp [] ys = []" |
"multp (x#xs) ys = addp (multp_const x ys) (0 # multp xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const c) = [c]" |
"coeffs (Add e1 e2) = addp (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = multp (coeffs e1) (coeffs e2)" 

(*Lemas auxiliares con simp y la regla de inducción correcta*)
lemma evalp_addp[simp]: "evalp (addp xs ys) x = evalp xs x + evalp ys x"
  apply (induction xs ys rule: addp.induct) (*Inducción sobre el esquema de la función*)
  apply (auto simp add: algebra_simps)
  done

lemma evalp_multp_const[simp]: "evalp (multp_const c xs) x = c * evalp xs x"
  apply (induction xs)
  apply (auto simp add: algebra_simps)
  done

lemma evalp_multp[simp]: "evalp (multp xs ys) x = evalp xs x * evalp ys x"
  apply (induction xs)
  apply (auto simp add: algebra_simps) (*Ya no se necesitan referenciar los lemas anteriores porque son simp*)
  done

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x" 
  apply (induction e)
  apply (auto) (*Se resuelve automáticamente gracias a que los lemas de arriba son simp*)
  done

end