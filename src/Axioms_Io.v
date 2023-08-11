(*
Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs LTS IO_Stubs.

Require Import ErrorStMonad_Coq.

Require Import List.
Import ListNotations.

(** IO Axioms *)

(*
Definition doRemote_session (t:Term) (pTo:Plc) (e:EvC) : EvC.
Admitted.

Definition parallel_vm_thread (l:Loc) (t:Term) (p:Plc) (e:EvC) : EvC.
Admitted.
*)

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Definition cvm_events_core (t:Core_Term) (p:Plc) (e:Evidence) : list Ev. 
Admitted.

Definition cvm_evidence_core (t:Core_Term) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition cvm_events (t:Term) (p:Plc) (e:Evidence) : list Ev :=
  cvm_events_core (copland_compile t) p e.

Definition cvm_evidence (t:Term) (p:Plc) (e:EvC) : EvC :=
  cvm_evidence_core (copland_compile t) p e.


Axiom remote_LTS: forall t annt n et i i',
    annoP_indexed annt t i i' ->
    lstar (conf annt n et) (cvm_events t n et) (stop n (aeval annt n et)).

(*
Axiom remote_Evidence_Type_Axiom: forall t n bits et,
    get_et (doRemote_session t n (evc bits et)) = eval t n et.
*)

(*
Axiom at_evidence : forall t (p:Plc) (e:EvC),
    doRemote_session t p e = cvm_evidence t p e.
*)

Axiom par_evidence : forall t (p:Plc) (e:EvC) loc,
    parallel_vm_thread loc (copland_compile t) p e = cvm_evidence t p e.



Axiom bpar_shuffle : forall x annt2 i i' tr p t1 t2 et1 et2,
    annoP_indexed annt2 t2 i i' ->
    lstar (conf t1 p et1) tr (stop p (aeval t1 p et1)) ->
    lstar (bp x (conf t1 p et1) (conf annt2 p et2))
          (shuffled_events tr
                           (cvm_events t2 p et2))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval annt2 p et2))).

Axiom thread_bookend_peel: forall (t:AnnoTerm) p (*et*) etr l (a:Core_Term) tr,
    (*lstar (conf t p et) tr (stop p (aeval t p et)) -> *)
    ([cvm_thread_start l p a etr] ++ tr ++ [cvm_thread_end l] =
     (shuffled_events tr (cvm_events_core a p etr))
    ).

Axiom events_cvm_to_core_mt : forall t p e,
    cvm_events_core (lseqc (aspc CLEAR) t) p e = cvm_events_core t p mt.


(** * Axiom:  assume parallel CVM threads preserve well-formedness of EvC bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

Axiom ev_cvm_mtc: forall ct p e loc,
    parallel_vm_thread loc ct p mt_evc = parallel_vm_thread loc (lseqc (aspc CLEAR) ct) p e.


Axiom cvm_evidence_correct_type : forall t p e e',
    cvm_evidence t p e = e' -> 
    get_et e' = eval t p (get_et e).

(** * Axiom about "simulated" parallel semantics of CVM execution:
      Executing a "CLEAR" before a term is the same as executing that term with mt initial evidence.
      TODO:  can we use existing axioms to prove this? *)
Axiom par_evidence_clear: forall l p bits et t2,
    parallel_vm_thread l (lseqc (aspc CLEAR) t2) p (evc bits et) =
    parallel_vm_thread l t2 p mt_evc.