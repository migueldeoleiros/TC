(*
- Miguel López López
- Teoría da Computación
- Práctica 2
*)

(*------------------------------------------------------------------------------------*)
(* Set-up *)
#load "ocaml-talf/src/talf.cma";;
#directory "ocaml-talf/src";;
open List;;
open Conj;;
open Auto;;
open Ergo;;
open Graf;;

(*------------------------------------------------------------------------------------*)
(*ejemplos*)
  let ap = Ap (Conjunto [Estado "0"; Estado "1"; Estado "2"], (*conjunto de estados*)

      Conjunto [Terminal "a"; Terminal "b"], (*alfabeto de entrada*)

      Conjunto [No_terminal ""; No_terminal "S"], (*alfabeto de la pila*)

      Estado "0", (*estado inicial*)

      (*funcion de transicion*)
      Conjunto [Arco_ap (Estado "0", Estado "1", Terminal "", No_terminal "",
                         [No_terminal "S"; No_terminal ""]);
                Arco_ap (Estado "1", Estado "1", Terminal "a", Terminal "a",
                         []);
                Arco_ap (Estado "1", Estado "1", Terminal "b", Terminal "b",
                         []);
                Arco_ap (Estado "1", Estado "1", Terminal "", No_terminal "S",
                         [Terminal "a"; No_terminal "S"]);
                Arco_ap (Estado "1", Estado "1", Terminal "", No_terminal "S",
                         [Terminal "b"; No_terminal "S"]);
                Arco_ap (Estado "1", Estado "1", Terminal "", No_terminal "S",
                         []);
                Arco_ap (Estado "1", Estado "2", Terminal "", No_terminal "",
                         [No_terminal ""])],

      No_terminal "", (*simbolo de inico de pila*)

      Conjunto [Estado "2"]);; (*estados finales*)

  let gic = Gic (Conjunto [No_terminal "S"], (*simbolos no terminales*)

       Conjunto [Terminal "a"; Terminal "b"], (*simbolos terminales*)

       Conjunto [ (*reglas de produccion*)
           Regla_gic (No_terminal "S", [Terminal "a"; No_terminal "S"]);
           Regla_gic (No_terminal "S", [Terminal "b"; No_terminal "S"]);
           Regla_gic (No_terminal "S", [])],

       No_terminal "S");; (*simbolo inicial*)

(*-----------------------------------------------------------------------------------*)
(*Ejercicio 1*)
   let ap_of_gic = function
       Gic (Conjunto n, Conjunto t, Conjunto p, No_terminal s) ->
        let rec aux1 acum = function
            [] -> acum
          | Regla_gic (No_terminal x, l) :: t ->
             aux1 ((Arco_ap (Estado "1", Estado "1", Terminal "", No_terminal x, l)) :: acum) t
          | _ -> raise (Failure "ap_of_gic: la gramatica no es regular")

        in
        let rec aux2 acum = function
            [] -> acum
          | Terminal x :: t ->
             aux2 ((Arco_ap (Estado "1", Estado "1", Terminal x, Terminal x, [])) :: acum) t;
          | _ -> raise (Failure "ap_of_gic: la gramatica no es regular")
        in
        let
          pila =
          Arco_ap (Estado "0", Estado "1", Terminal "", No_terminal "",
                   [No_terminal s; No_terminal ""]) ::
          (aux1 [] p) @
          (aux2 [] t) @
          [Arco_ap (Estado "1", Estado "2", Terminal "", No_terminal "", [No_terminal ""])]
        in
        Ap (Conjunto [Estado "0"; Estado "1"; Estado "2"], (*conjunto de estados*)
            Conjunto t,                                    (*alfabeto de entrada*)
            Conjunto (No_terminal ""::n),                  (*alfabeto de la pila*) 
            Estado "0",                                    (*estado inicial*)
            Conjunto pila,                                 (*funcion de tansicion*)
            No_terminal "",                                (*simbolo de inicio de pila*) 
            Conjunto [Estado "2"])                         (*estados finales*)
     | _ -> raise (Failure "ap_of_gic: el axioma de la gramatica es un terminal");;

   (*ejemplo*)
   ap_of_gic gic;;

(*-----------------------------------------------------------------------------------*)
(*Ejercicio 2*)

  (*funciones auxiliares*)
  exception No_encaja;;

  let encaja (estado, cadena, pila_conf) (Arco_ap (origen, destino, entrada, cima, pila_arco)) =
    let
      nuevo_estado =
      if estado = origen then (*Arco tiene el origen adecuado*)
        destino
      else
        raise No_encaja
    and
      nueva_cadena =
      if entrada = Terminal "" then (*entrada es epsilon*)
        cadena
      else
        if (cadena <> []) && (entrada = hd cadena) then (*entrada coincide con cadena*)
          tl cadena
        else
          raise No_encaja
    and
      nueva_pila_conf =
      if cima = Terminal "" then (*cima del arco es espsilon*)
        pila_arco @ pila_conf
      else
        if (pila_conf <> []) && (cima = hd pila_conf) then (*cima del arco coincide con pila*)
          pila_arco @ (tl pila_conf)
        else
          raise No_encaja
    in
    (nuevo_estado, nueva_cadena, nueva_pila_conf);;

  let es_conf_final finales = function
      (estado, [], _) -> pertenece estado finales (*estado es final y cadena vacia*)
    | _ -> false;;


  (*Respuesta*)

  (*
   * La funcion retornará todos los arcos que encajen durante el escaner.
   * Esto significa que también retornará arcos que no llevan al resultado true
   * pero que se recorren durante el escaner. 
   *)
  let escaner_ap_reglas cadena (Ap (_, _, _, inicial, Conjunto delta, zeta, finales)) =
    let rec aux = function
        ([], [], _, reglas_activadas) -> (false, rev reglas_activadas)
      | ([], l, _, reglas_activadas) -> aux (l, [], delta, reglas_activadas)
      | (_::cfs, l, [], reglas_activadas) -> aux (cfs, l, delta, reglas_activadas)
      | (cf::cfs, l, a::arcos, reglas_activadas) ->
         try
           let
             ncf = encaja cf a
           in
           if es_conf_final finales ncf then
             (true, rev (a :: reglas_activadas))
           else
             aux (cf::cfs, ncf::l, arcos, a::reglas_activadas)
         with
           No_encaja -> aux (cf::cfs, l, arcos, reglas_activadas)
    in
    aux ([(inicial, cadena, [zeta])], [], delta, []) ;;

  (*
   * Esta función además de los arcos retorna la configuración que que encaja con dicho arco,
   * lo que es util para entender un poco mejor porqué, como expliqué en la anterior función,
   * también se retornan arcos que no son parte del camino de procesamiento final. 
   *)
  let escaner_ap_test cadena (Ap (_, _, _, inicial, Conjunto delta, zeta, finales)) =
    let rec aux = function
        ([], [], _, reglas_activadas) -> (false, rev reglas_activadas)
      | ([], l, _, reglas_activadas) -> aux (l, [], delta, reglas_activadas)
      | (_::cfs, l, [], reglas_activadas) -> aux (cfs, l, delta, reglas_activadas)
      | (cf::cfs, l, a::arcos, reglas_activadas) ->
         try
           let
             ncf = encaja cf a
           in
           if es_conf_final finales ncf then
             (true, rev ((cf, a):: reglas_activadas))
           else
             aux (cf::cfs, ncf::l, arcos, (cf, a)::reglas_activadas)
         with
           No_encaja -> aux (cf::cfs, l, arcos, reglas_activadas)
    in
    aux ([(inicial, cadena, [zeta])], [], delta, []);;

  (*ejemplo*)
  escaner_ap_reglas (cadena_of_string "a") ap;;
