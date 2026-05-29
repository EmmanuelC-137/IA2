theory Examen_P3
  imports Main
begin

text \<open>Definiciones\<close>
text \<open>Ejercicio 1\<close>
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval [] = []" |
"eval  "



(*lemma "eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"
by auto *)


text \<open>Ejercicio 2\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
fun contents :: "'a tree \<Rightarrow> 'a list" where

fun sum_tree :: "'a tree \<Rightarrow> a" where


text \<open>Ejercicio 3\<close>

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

fun sumN :: "aexp \<Rightarrow> int" where



