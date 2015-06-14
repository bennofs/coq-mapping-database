Require MappingDB_avl.
Require MappingDB.
Cd "extract".

Require ExtrOcamlBasic.
Require ExtrOcamlZInt.

Require Import NArith.

(* This is the only dependency remaining on N. Inlining gets rid of the dependency. 
 *
 * Note that we need to supply a definition of N.compare using parentheses here, since
 * coq is not smart enough to automatically insert parentheses when inlining, which
 * produces invalid ocaml code.
 *)
Extract Constant N.compare=>"(fun x y -> if x=y then Eq else if x<y then Lt else Gt)".

(* Blacklist the List name, since OCaml uses the same name for it's list module.  *)
Extraction Blacklist List. 
(* Change to the extraction directory, so the generated files do not clutter the 
 * source directory 
 *)

(* Extract AVL implementation and assoc list implementation.
 * 
 * Separate makes sure that everything gets extracted to different files, which results
 * in much cleaner code and allows to get rid of all the NArith bloat 
 * (the extracted NArith file can be ignored, since it is not used by anything).
 *)
Separate Extraction MappingDB_avl MappingDB AVLTree AssocList.
