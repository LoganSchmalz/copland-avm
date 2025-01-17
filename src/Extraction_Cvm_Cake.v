Require Extraction.

Require Import Term_Defs Term_Defs_Core Cvm_Run IO_Stubs AM_Monad.
Require Import CopParser.

Require Import Example_Phrases Example_Phrases_Demo.

Require Import privPolicy Manifest_Generator Manifest_Compiler.

Require Import Client_AM Server_AM.


Require Import List.
Import ListNotations.

Extraction Language CakeML. (* OCaml. *) 

(*
Unset Extraction Optimize.
*)

Extract Inductive nat => "nat" ["O" "S"].
Extract Inductive bool => "bool" ["True" "False"].
Extract Inductive option => "option" ["Some" "None"].

Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
(*Extract Inductive prod => "( * )" [ "" ]. *)

(*
Extraction Implicit do_asp [3 4].
Extraction Implicit do_asp' [3 4]. 
*)
Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].


Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".
(* Extract Constant + => "add". *)
(* Extract Constant Nat.add => "(+)". *)

Definition term_list : list Term := 
	[cert_style; cert_style_test; cert_style_trimmed; cert_cache_p1; cert_cache_p0; cert_cache_p0_trimmed].

Separate Extraction run_cvm manifest_compiler  
		    run_am_app_comp 
			handle_AM_request am_client_auth am_client_gen 
			term_list ssl_sig_parameterized kim_meas
		    par_mut_p0 par_mut_p1 layered_bg_strong
		    man_gen_run_attify empty_am_result.
