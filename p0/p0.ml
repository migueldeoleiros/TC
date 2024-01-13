(*
- Miguel López López
- Teoría da Computación
- Práctica 0
*)

(* ----------------------------------------------------------- *)
(* Ejercicio 1 *)

(*Uso una función recursiva en la que se coge el primer elemento
  y se le aplica la funcion 1 y se llama de nuevo a la función esta
  vez siendo la función 2 y la lista que queda.*)
let rec mapdoble f1 f2 = function
    [] -> []
  | h::[] -> [f1 h]
  | h::t -> f1(h)::mapdoble f2 f1 t;;

(*val mapdoble : ('a -> 'b) -> ('a -> 'b) -> 'a list -> 'b list = <fun>*)

(*
1 | mapdoble (function x -> x*2) (function x -> "x") [1;2;3;4;5];;;;
                                                ^^^
Error: This expression has type string but an expression was expected of type
         int
*)

(*let y = function x -> 5 in mapdoble y;;*)
(*- : ('_weak1 -> int) -> '_weak1 list -> int list = <fun>*)

(* ----------------------------------------------------------- *)
(* Ejercicio 2 *)
(*val primero_que_cumple : ('a -> bool) -> 'a list -> 'a = <fun>*)
let rec primero_que_cumple f = function
    [] -> raise Not_found
  | h::t -> if f(h) = true then h else primero_que_cumple f t;;

(*val existe : 'a -> 'b -> bool = <fun>*)
let existe f l = 
    try (let _ = primero_que_cumple in true)
    with Not_found -> false;;

(*val asociado : ('a * 'b) list -> 'c -> 'b = <fun>*)
let asociado l key = 
  snd(primero_que_cumple(function(a,b) -> a = key) l);;

(* ----------------------------------------------------------- *)
(* Ejercicio 3 *)
type 'a arbol_binario =
    Vacio
  | Nodo of 'a * 'a arbol_binario * 'a arbol_binario;;

let tree = Nodo(3,Nodo(2,Vacio,Vacio),Nodo(5,Nodo(4,Vacio,Vacio),Nodo(1,Vacio,Vacio)));;

let rec in_orden = function
    Vacio -> []
  | Nodo (head, left, right) -> (in_orden left) @ (head::(in_orden right));;

in_orden tree;;
(*- : int list = [2; 3; 4; 5; 1]*)

let rec pre_orden = function
    Vacio -> []
  | Nodo (head, left, right) -> head::(pre_orden left) @ ((pre_orden right));;

pre_orden tree;;
(*- : int list = [3; 2; 5; 4; 1]*)

let rec post_orden = function
    Vacio -> []
  | Nodo (head, left, right) -> (post_orden left) @ ((post_orden right) @ [head]);;

post_orden tree;;
(*- : int list = [2; 4; 1; 5; 3]*)

let anchura tree =
  let rec aux queue l = match queue with
    | [] -> List.rev l
    | Nodo(head, left, right) :: rest ->
       let new_queue = rest @ [left; right] in
       aux new_queue (head :: l)
    | Vacio :: rest -> aux rest l
  in aux [tree] [];;

anchura tree;;
(*- : int list = [3; 2; 5; 4; 1]*)

(* ----------------------------------------------------------- *)
(* Ejercicio 4 *)
type 'a conjunto = Conjunto of 'a list;;

let c1 = Conjunto([1;2;3;4;5]);;
let c2 = Conjunto([4;5;6;7;8]);;

(*val pertenece : 'a -> 'a conjunto -> bool = <fun>*)
let rec pertenece x = function
    Conjunto [] -> false
  | Conjunto (h::t) -> if h=x then true else pertenece x (Conjunto t);;

pertenece 1 c1;;
(*: true*)

pertenece 9 c1;;
(*: false*)

(*val agregar : 'a -> 'a conjunto -> 'a conjunto = <fun>*)
let rec agregar x c =
  if pertenece x c then c else match c with
  Conjunto l -> (Conjunto (x::l));;

agregar 1 c1;;
(*: Conjunto [1; 2; 3; 4; 5]*)

agregar 9 c1;;
(*: Conjunto [9; 1; 2; 3; 4; 5]*)

(*val conjunto_of_list : 'a list -> 'a conjunto = <fun>*)
let conjunto_of_list l =
  let rec aux (Conjunto l2) = function
      [] -> (Conjunto l2)
    | h::t -> aux (agregar h (Conjunto l2)) t
  in aux (Conjunto []) l;;

conjunto_of_list [1;3;2;4;5;1;2;3;9];;
(*: Conjunto [9; 5; 4; 2; 3; 1]*)

(*val suprimir : 'a -> 'a conjunto -> 'a conjunto = <fun>*)
let suprimir x (Conjunto l) =
  let rec aux x = function
      [] -> [] 
    | h::t -> if h=x then t else h::(aux x t)
  in Conjunto (aux x l);;

suprimir 3 c1;;
(*: Conjunto [1; 2; 4; 5]*)

(*val cardinal : 'a conjunto -> int = <fun>*)
let cardinal (Conjunto l) =
  let rec aux count = function
      [] -> count 
    | _::t -> aux (count+1) t
  in aux 0 l;;

cardinal c1;;
(*: 5*)

(*val union : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)
let union c1 (Conjunto l2) =
  let rec aux (Conjunto l1) = function
      [] -> l1 
    | h::t -> if pertenece h c1 then (aux c1 t) else h::(aux (Conjunto l1) t)
  in Conjunto (aux c1 l2);;

union c1 c2;;
(*: Conjunto [6; 7; 8; 1; 2; 3; 4; 5]*)

(*val interseccion : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)
let interseccion c1 (Conjunto l2) =
  let rec aux (Conjunto l1) = function
      [] -> [] 
    | h::t -> if pertenece h c1 then h::(aux c1 t) else (aux (Conjunto l1) t)
  in Conjunto (aux c1 l2);;

interseccion c1 c2;;
(*: Conjunto [4; 5]*)

(*val diferencia : int conjunto -> int conjunto -> int conjunto = <fun>*)
let diferencia (Conjunto l1) c2 =
  let rec aux (Conjunto l2) = function
      [] -> [] 
    | h::t -> if pertenece h c2 then (aux c1 t) else h::(aux (Conjunto l2) t)
  in Conjunto (aux c2 l1);;

diferencia c1 c2;;
(*: Conjunto [1; 2; 3]*)

(*val incluido : 'a conjunto -> 'a conjunto -> bool = <fun>*)
let rec incluido (Conjunto l1) c2 = match l1 with
    [] -> true 
  | h::t -> if pertenece h c2 then (incluido (Conjunto t) c2) else false;;

incluido c1 c2;;
(*: false*)

incluido c1 (Conjunto [0;1;2;3;4;5;6;7;8;9]);;
(*: true*)

(*val igual : int conjunto -> int conjunto -> bool = <fun>*)
let igual c1 c2 =
  (diferencia c1 c2) = (diferencia c2 c1);;

igual c1 c2;;
(*: false*)

igual c1 c1;;
(*: true*)

(*val producto_cartesiano : 'a conjunto -> 'b conjunto -> ('a * 'b) conjunto = <fun>*)
let producto_cartesiano (Conjunto l1) (Conjunto l2)=
  let rec aux l1 l2 laux = match l1,l2 with
      [],_ -> []
    | (h::t),([]) -> aux t laux laux
    | (h1::t1), (h2::t2) -> (h1,h2)::(aux l1 t2 laux)
  in Conjunto (aux l1 l2 l2);;

producto_cartesiano c1 c2;;
(*
: Conjunto
:  [(1, 4); (1, 5); (1, 6); (1, 7); (1, 8); (2, 4); (2, 5); (2, 6); (2, 7);
:   (2, 8); (3, 4); (3, 5); (3, 6); (3, 7); (3, 8); (4, 4); (4, 5); (4, 6);
:   (4, 7); (4, 8); (5, 4); (5, 5); (5, 6); (5, 7); (5, 8)]
*)

(*val list_of_conjunto : 'a conjunto -> 'a list = <fun>*)
let list_of_conjunto (Conjunto l) = l;;

list_of_conjunto c1;;
(*| 1 | 2 | 3 | 4 | 5 |*)
