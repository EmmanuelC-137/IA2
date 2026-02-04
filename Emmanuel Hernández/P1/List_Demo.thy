theory List_Demo
imports Main
begin

(* datatype 'a list = Nil | Cons "'a" "'a list"

term "Nil"

declare[[names_short]]

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

value "app (Cons (1::nat) (Cons 2 Nil)) (Cons 3 (Cons 4 Nil))"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (app (Cons (1::nat) (Cons 2 Nil)) (Cons 3 (Cons 4 Nil)))"


lemma "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  by (auto)

lemma "rev (rev xs) = xs"
  apply (induction xs) *)

(* cometario *)

term "Nil"

declare[[names_short]]

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app [] ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

value "app [1,2] [3,4::nat]"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (app [1,2][3,4 :: nat])"

lemma l1: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  by (auto)

lemma l2: "app ys [] = ys"
  by (induction ys, auto)

lemma l3: "rev (app xs ys) = app (rev ys)(rev xs)"
  apply(induction xs)
  by(auto simp add: l1 l2)

lemma "rev (rev xs) = xs"
  apply (induction xs)
  by (auto simp add: l3)

value "length [1,2,3::nat,4]"

fun len :: "'a list \<Rightarrow> nat" where
"len [] = 0" |
"len (x # xs) = 1 + (len xs)"

value "len [1,2,3::nat,4]"

fun mapp :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where

"mapp f [] = []" |
"mapp f (x#xs) = f x # mapp f xs"

value "mapp (\<lambda>x. x * x) [1,2,3::nat]"

(* Intentar hacer la demotracion de esto de abajo *)
lemma "length (xs @ ys) = length xs + length ys"
  apply (induction xs)
  by (auto)

lemma "map f (xs @ ys) = map f xs @ map f ys"
  apply (induction xs)
  by (auto)

end