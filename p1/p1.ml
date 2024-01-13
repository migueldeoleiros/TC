(*
- Miguel López López
- Teoría da Computación
- Práctica 1
*)

(* ----------------------------------------------------------- *)
(* Set-up *)
#load "ocaml-talf/src/talf.cma";;
#directory "ocaml-talf/src";;
open Conj;;
open Auto;;
open Ergo;;
open Graf;;

(* ----------------------------------------------------------- *)
(*Ejercicio 1 a*)
(*val es_afne : Auto.af -> bool = <fun>*)
let es_afne (Af (estados, alfabeto, e_ini, arcos, e_fin)) = 
  let rec aux = function 
    | Conjunto [] -> false
    | _ -> true
  in aux (avanza (Terminal "") estados (Af (estados, alfabeto, e_ini, arcos, e_fin)));;

(*Ejemplos*)
let afne = Af (
    Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"], (*estados*)

    Conjunto [Terminal "a"; Terminal "b"; Terminal "c"], (*alfabeto*)

    Estado "0", (*estado inicial*)

    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a"); (*funcion de transicion*)
    Arco_af (Estado "1", Estado "1", Terminal "b");
    Arco_af (Estado "1", Estado "2", Terminal "a");
    Arco_af (Estado "2", Estado "0", Terminal "");
    Arco_af (Estado "2", Estado "3", Terminal "c")],

    Conjunto [Estado "1"; Estado "3"] (*estados finales*)
  );;

es_afne afne;; (*true*)

let afn = Af (
    Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"], (*estados*)

    Conjunto [Terminal "a"; Terminal "b"; Terminal "c"], (*alfabeto*)

    Estado "0", (*estado inicial*)

    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a"); (*funcion de transicion*)
    Arco_af (Estado "1", Estado "1", Terminal "b");
    Arco_af (Estado "1", Estado "2", Terminal "a");
    Arco_af (Estado "2", Estado "0", Terminal "a");
    Arco_af (Estado "2", Estado "3", Terminal "a");
    Arco_af (Estado "2", Estado "3", Terminal "c")],

    Conjunto [Estado "1"; Estado "3"] (*estados finales*)
  );;

es_afne afn;; (*false*)

(* ----------------------------------------------------------- *)
(*Ejercicio 1 b*)
(*val get_simbols : Auto.estado -> Auto.arco_af Conj.conjunto -> Auto.simbolo list = <fun>*)
let get_simbols estado (Conjunto arcos) = 
  let rec aux arcs sim = match arcs with 
    | [] -> sim
    | (Arco_af (e, d, s))::t -> if (e=estado) then (aux t (s::sim)) else (aux t sim)
  in aux arcos [];;

(*val es_afn : Auto.af -> bool = <fun>*)
let es_afn (Af (Conjunto estados, alfabeto, e_ini, arcos, e_fin)) =
  let rec aux = function
    | [] -> false
    | h::t ->
       let simbols = (get_simbols h arcos) in 
       if (List.length simbols) = (cardinal (conjunto_of_list(simbols))) then (*Comprobación item repetido*)
         aux t
       else
         true
  in aux estados;;

(*Ejemplo*)
let afn = Af (
    Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"], (*estados*)

    Conjunto [Terminal "a"; Terminal "b"; Terminal "c"], (*alfabeto*)

    Estado "0", (*estado inicial*)

    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a"); (*funcion de transicion*)
    Arco_af (Estado "1", Estado "1", Terminal "b");
    Arco_af (Estado "1", Estado "2", Terminal "a");
    Arco_af (Estado "2", Estado "0", Terminal "a");
    Arco_af (Estado "2", Estado "3", Terminal "a");
    Arco_af (Estado "2", Estado "3", Terminal "c")],

    Conjunto [Estado "1"; Estado "3"] (*estados finales*)
  );;

es_afn afn;; (*true*)

(* ----------------------------------------------------------- *)
(*Ejercicio 1 c*)
(*val es_afd : Auto.af -> bool = <fun>*)
let es_afd (Af (Conjunto estados, alfabeto, e_ini, arcos, e_fin)) =
  let num_estados = List.length estados in
  let num_simbolos = cardinal alfabeto in
  let num_arcos = cardinal arcos in
  let is_non_determinism = es_afn (Af (Conjunto estados, alfabeto, e_ini, arcos, e_fin)) in
  let is_full_deterministic = num_arcos = num_estados * num_simbolos in
  is_full_deterministic && (not is_non_determinism);;

(*Ejemplo*)
let afd = Af (
    Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"], (*estados*)

    Conjunto [Terminal "a"; Terminal "b"], (*alfabeto*)

    Estado "0", (*estado inicial*)

    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a"); (*funcion de transicion*)
    Arco_af (Estado "0", Estado "0", Terminal "b");
    Arco_af (Estado "1", Estado "1", Terminal "b");
    Arco_af (Estado "1", Estado "2", Terminal "a");
    Arco_af (Estado "2", Estado "0", Terminal "a");
    Arco_af (Estado "3", Estado "3", Terminal "a");
    Arco_af (Estado "3", Estado "3", Terminal "b");
    Arco_af (Estado "2", Estado "3", Terminal "b")],

    Conjunto [Estado "1"; Estado "3"] (*estados finales*)
  );;

es_afd afd;; (*true*)

(* ----------------------------------------------------------- *)
(*Ejercicio 2*)
(*val siguiente : Auto.estado -> Auto.simbolo -> Auto.arco_af list -> Auto.estado = <fun>*)
let rec siguiente estado simbolo = function
  | [] -> estado;
  | h :: t ->
     match h with Arco_af (origen, destino, simbolo_arco) ->
       if (origen = estado) && (simbolo_arco = simbolo) then destino
       else siguiente estado simbolo t ;;

(*val equivalentes : Auto.af -> Auto.af -> bool = <fun>*)
let equivalentes (Af (estados1, alfabeto1, e_ini1, arcos1, e_fin1))
                 (Af (estados2, alfabeto2, e_ini2, arcos2, e_fin2)) = 
  let alfabeto = Conj.union alfabeto1 alfabeto2 in
  let queue = Queue.create () in
  Queue.add (e_ini1, e_ini2) queue;
  let rec consume queue visitados =
    if Queue.is_empty queue then true
    else
      let estado_actual = Queue.pop queue in
      if Conj.pertenece estado_actual visitados then
        consume queue visitados
      else
        if not ((Conj.pertenece (fst estado_actual) e_fin1) = (Conj.pertenece (snd estado_actual) e_fin2)) then
          false
        else
          let rec procesar = function
            | [] -> consume queue (Conj.agregar estado_actual visitados)
            | h :: t ->
               let nuevo_estado1 = siguiente (fst estado_actual) h (Conj.list_of_conjunto arcos1) in
               let nuevo_estado2 = siguiente (snd estado_actual) h (Conj.list_of_conjunto arcos2) in
               Queue.add (nuevo_estado1, nuevo_estado2) queue;
               procesar t
          in
          procesar (Conj.list_of_conjunto alfabeto);
  in consume queue Conj.conjunto_vacio;;

(*Ejemplos*)
let af1 = Af (
    Conjunto [Estado "0"; Estado "1"; Estado "2"], (*estados*)

    Conjunto [Terminal "a"; Terminal "b"], (*alfabeto*)

    Estado "0", (*estado inicial*)

    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a"); (*funcion de transicion*)
    Arco_af (Estado "1", Estado "1", Terminal "b");
    Arco_af (Estado "1", Estado "2", Terminal "a");
    Arco_af (Estado "2", Estado "2", Terminal "b")],

    Conjunto [Estado "2"] (*estados finales*)
  );;

equivalentes af1 af1;; (*true*)

let af2 = Af (
    Conjunto [Estado "0"; Estado "1"; Estado "2"], (*estados*)

    Conjunto [Terminal "a"; Terminal "b"], (*alfabeto*)

    Estado "0", (*estado inicial*)

    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a"); (*funcion de transicion*)
    Arco_af (Estado "1", Estado "2", Terminal "b");
    Arco_af (Estado "1", Estado "2", Terminal "a");
    Arco_af (Estado "2", Estado "2", Terminal "b")],

    Conjunto [Estado "2"] (*estados finales*)
  );;

equivalentes af1 af2;; (*false*)

let af11 = Af (
    Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"], (*estados*)

    Conjunto [Terminal "a"; Terminal "b"], (*alfabeto*)

    Estado "0", (*estado inicial*)

    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a"); (*funcion de transicion*)
    Arco_af (Estado "1", Estado "1", Terminal "b");
    Arco_af (Estado "1", Estado "2", Terminal "a");
    Arco_af (Estado "0", Estado "3", Terminal "b");
    Arco_af (Estado "2", Estado "3", Terminal "a");
    Arco_af (Estado "2", Estado "2", Terminal "b")],

    Conjunto [Estado "2"] (*estados finales*)
  );;
