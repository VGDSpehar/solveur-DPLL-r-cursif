open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let simplifie l clauses =
  (* fonction pour filtrer l d'une clause*)
  let filtrer_l clause =
    (* on supprime la clause si elle contient l*)
    if List.mem l clause then None
    else 
      (* on enlève  non l de la clause *)
      Some(let enlever_l lit = if lit = -l then None else Some(lit)
      in filter_map enlever_l clause)
    in filter_map filtrer_l clauses

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
  match clauses with
  | [] -> raise Not_found
  | [lit]::r -> lit
  | _::tl -> unitaire tl
;;

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)

(* remove_e_from_l : int -> list int -> list int
   enlève un entier e et son opposé d'une liste d'entier
   est utilisée dans pur*)

let remove_e_from_l e l =
    filter_map(fun x -> if (e = x || e = -x) then None else Some(x) ) l
;;

exception Failure of string;;

let pur clauses = 
   (* fonction auxiliare qui passe au crible une liste : 
     on examine si le premier élément est pur, 
     sinon on enlève de la liste les éléments égaux et leurs opposés
     puis on recommence avec la liste privée du premier élément*)
  let rec crible liste =
    match liste with 
    | [] -> raise(Failure "pas de littéral pur")
    | hd::tl -> if not(List.mem (-hd) tl) then hd else crible(remove_e_from_l hd tl)
  in crible (List.flatten clauses)
;;

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
    (* un clause vide n'est jamais satisfiable *)
    if List.mem [] clauses then None else
      (*on teste d'abord pour les clauses unitaires*)
    match ( try Some(unitaire clauses) with Not_found -> None) with
      | Some lit-> solveur_dpll_rec (simplifie (lit) clauses) (lit::interpretation)
      (* Si pas de clauses unitaires on teste pour voir si il existe un littéral pur*)
      | None -> match (try Some(pur clauses) with Failure "pas de littéral pur" -> None) with 
        | Some lit -> (solveur_dpll_rec (simplifie lit clauses) (lit::interpretation)) 
        (* Sinon on effectue la même opération que dans solveur_split*)
        | None -> let lit = hd (hd clauses) in
              let branche = solveur_dpll_rec (simplifie lit clauses) (lit::interpretation) in
              match branche with
              | None -> solveur_dpll_rec (simplifie (-lit) clauses) ((-lit)::interpretation)
              | _    -> branche
    

;; 


(* tests *)
(*let () = print_modele (solveur_dpll_rec exemple_7_2 []);;*)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

(* let rec print_list list =
  match list with
  |[] -> print_newline ()
  | e::l -> print_int e ; print_string " " ; print_list l
;;
*)