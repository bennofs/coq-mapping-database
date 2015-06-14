open Printf
open Sys

let rec go_avl i n acc = 
  let x = Random.int 10000000 in
  if i > n then acc else go_avl (i + 1) n (AVLTree.avl_insert x x acc)

let compute_avl n = 
  let r = go_avl 0 n AVLTree.Avl_empty in
  match AVLTree.avl_lookup n r with
    | None -> printf "0:" 
    | Some f -> printf "%i:" f

let rec go_assoc i n acc = 
  let x = Random.int 10000000 in
  if i > n then acc else go_assoc (i + 1) n (AssocList.al_insert x x acc)

let compute_assoc n = 
  let r = go_assoc 0 n AssocList.al_empty in
  match AssocList.al_assoc n r with
    | None   -> printf "0:"
    | Some f -> printf "%i:" f

let run name f =
  for i = 0 to 100 do
      let startTime = time () in
      let () = f (i * 100) in
      let endTime = time () in
      printf "%s:%i:%f" name (i * 100) (endTime -. startTime);
      print_newline ()
  done

let () =
  Random.self_init ();
  run "avl" compute_avl;
  run "assoc" compute_assoc
