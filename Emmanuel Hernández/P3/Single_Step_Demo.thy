theory Single_Step_Demo
imports Main
begin

thm conjI[of "Hola mundo"]
thm conjI[of "5 = 6"]

(* Pruebas hacia adelante con OF*)

(* ?t = ?t: el valor que se establese es el mimso el lado derecho e izquierdo *)
thm refl

thm conjI
thm conjI[OF refl [of "a"]]
end