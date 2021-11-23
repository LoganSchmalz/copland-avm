(* Copland terms, events, and annotated terms *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** This module contains the basic definitions for Copland terms,
    events, and annotated terms. *)

Require Import PeanoNat Nat Compare_dec Lia.
Require Import Preamble StructTactics Defs.
Require Import AutoPrim.

Require Export BS.

Require Import List.
Import List.ListNotations.

Require Import Coq.Arith.Even Coq.Program.Tactics Coq.Program.Equality.

Require Import Coq.Bool.Bool.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


(** * Terms and Evidence

    A term is either an atomic ASP, a remote call, a sequence of terms
    with data a dependency, a sequence of terms with no data
    dependency, or parallel terms. *)

(** [Plc] represents a place. *)

Definition Plc: Set := nat.
Definition N_ID: Set := nat.

Definition Event_ID: Set := nat.


Definition ASP_ID: Set.
Admitted.
Definition TARG_ID: Set.
Admitted.
Definition Arg: Set.
Admitted.

Definition eq_aspid_dec:
  forall x y: ASP_ID, {x = y} + {x <> y}.
Proof.
Admitted.

Definition eq_targid_dec:
  forall x y: TARG_ID, {x = y} + {x <> y}.
Proof.
Admitted.

Definition eq_arg_dec:
  forall x y: Arg, {x = y} + {x <> y}.
Proof.
Admitted.

Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

Definition eqb_asp_params: ASP_PARAMS -> ASP_PARAMS -> bool.
Admitted.

Definition eq_asp_params_dec:
  forall x y: ASP_PARAMS, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality.
  eapply eq_targid_dec.
  eapply eq_arg_dec.
  eapply eq_aspid_dec.
Defined.

Lemma eqb_asp_params_true_iff: forall a a0,
    eqb_asp_params a a0 = true <->
    a = a0.
Proof.
Admitted.

Inductive ASP: Set :=
| CPY: ASP
| ASPC: ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP.

Inductive SP: Set :=
| ALL
| NONE.

Definition Split: Set := (SP * SP).

Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

(** The structure of evidence. *)

Inductive Evidence: Set :=
| mt: Evidence
| uu: ASP_PARAMS -> Plc -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: N_ID -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

Fixpoint et_size (e:Evidence): nat :=
  match e with
  | mt => 0
  | uu _ _ e' => 1 + (et_size e')
  | gg _ e' => 1 + (et_size e')
  | hh _ _ => 1
  | nn _ => 1
  | ss e1 e2 => (et_size e1) + (et_size e2)
  | pp e1 e2 => (et_size e1) + (et_size e2)
  end.

Fixpoint thread_count (t:Term) : nat :=
  match t with
  | asp _ => 0
  | att _ _ => 0
  | lseq t1 t2 => max (thread_count t1) (thread_count t2)
  | bseq _ t1 t2 => max (thread_count t1) (thread_count t2)
  | bpar _ t1 t2 => 1 + (thread_count t1) + (thread_count t2)
  end.

(*
Compute (thread_count (bpar (ALL,ALL) (asp SIG) (asp CPY))).
 *)

Definition RawEv := list BS.

Inductive EvC: Set :=
| evc: RawEv -> Evidence -> EvC.

Definition mt_evc: EvC := (evc [] mt).

Definition get_et (e:EvC) : Evidence :=
  match e with
  | evc ec et => et
  end.

Definition get_bits (e:EvC): list BS :=
  match e with
  | evc ls _ => ls
  end.

Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall ls et,
    length ls = et_size et ->
    wf_ec (evc ls et).
    
    
Definition splitEv_T_l (sp:Split) (e:Evidence) : Evidence :=
  match sp with
  | (ALL,_) => e
  |  _ => mt
  end.

Definition splitEv_T_r (sp:Split) (e:Evidence) : Evidence :=
  match sp with
  | (_,ALL) => e
  |  _ => mt
  end.

Definition eval_asp t p e :=
  match t with
  | CPY => e 
  | ASPC params => uu params p e
  | SIG => gg p e
  | HSH => hh p e
  end.

(** The evidence associated with a term, a place, and some initial evidence. *)

Fixpoint eval (t:Term) (p:Plc) (e:Evidence) : Evidence :=
  match t with
  | asp a => eval_asp a p e
  | att q t1 => eval t1 q e
  | lseq t1 t2 => eval t2 p (eval t1 p e)
  | bseq s t1 t2 => ss (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  | bpar s t1 t2 => pp (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  end.


(** * Annotated Terms

    Annotated terms are used to ensure that each distinct event has a
    distinct natural number.  To do so, each term is annotated by a
    pair of numbers called a range.  Let [(i, k)] be the label for
    term [t].  The labels will be chosen to have the property such
    that for each event in the set of events associated with term [t],
    its number [j] will be in the range [i <= j < k].  *)

Definition Range: Set := nat * nat.

Inductive AnnoTerm: Set :=
| aasp: Range -> ASP -> AnnoTerm
| aatt: Range -> Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abpar: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.



(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  Each event is
    distinguished using a unique natural number.

 *)

Definition Loc: Set := nat.
Definition Locs: Set := list Loc.

Inductive Ev: Set :=
| copy:  nat -> Plc -> Ev 
| umeas: nat -> Plc -> ASP_PARAMS -> Ev
| sign: nat -> Plc -> Evidence -> Ev
| hash: nat -> Plc -> Evidence -> Ev
| req: nat -> Plc -> Plc -> Term -> Evidence -> Ev
| rpy: nat -> Plc -> Plc -> Evidence -> Ev 
| split: nat -> Plc -> Ev
| join:  nat -> Plc -> Ev
| cvm_thread_start: Loc -> Plc -> Term -> Evidence -> Ev
| cvm_thread_end: Loc -> Ev.

Definition eq_ev_dec:
  forall x y: Ev, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality;
    try (apply eq_arg_dec);
    try (apply eq_aspid_dec);
    try (apply eq_targid_dec).
Defined.
Hint Resolve eq_ev_dec : core.

(** The natural number used to distinguish events. *)

Definition ev x : nat :=
  match x with
  | copy i _ => i
  | umeas i _ _ => i
  | sign i _ _ => i
  | hash i _ _ => i
  | req i _ _ _ _ => i
  | rpy i _ _ _ => i 
  | split i _ => i
  | join i _ => i
  | cvm_thread_start _ _ _ _ => 42
  | cvm_thread_end _ => 43
  end.

(** The natural number indicating the place where an event occured. *)
Definition pl x : Plc :=
  match x with
  | copy _ p => p
  | umeas _ p _ => p
  | sign _ p _ => p
  | hash _ p _ => p
  | req _ p _ _ _ => p
  | rpy _ p _ _ => p
  | split _ p => p
  | join _ p => p
  | cvm_thread_start _ p _ _ => p
  | cvm_thread_end _ => 45
  end.

(** Events are used in a manner that ensures that
[[
    forall e0 e1, ev e0 = ev e1 -> e0 = e1.
]]
See Lemma [events_injective].
 *)


Definition asp_event i x p e :=
  match x with
  | CPY => copy i p
  | ASPC ps => umeas i p ps
  | SIG => sign i p e
  | HSH => hash i p e
  end.

Fixpoint esize t :=
  match t with
  | aasp _ _ => 1
  | aatt _ _ t1 => 2 + esize t1
  | alseq _ t1 t2 => esize t1 + esize t2
  | abseq _ _ t1 t2 => 2 + esize t1 + esize t2
  | abpar _ _ t1 t2 => 2 + esize t1 + esize t2
  end.

Definition range x :=
  match x with
  | aasp r _ => r
  | aatt r _ _ => r
  | alseq r _ _ => r
  | abseq r _ _ _ => r
  | abpar r _ _ _ => r
  end.

Inductive AnnoTermPar: Set :=
| aasp_par: ASP -> AnnoTermPar
| aatt_par: Plc -> Term -> AnnoTermPar
| alseq_par: AnnoTermPar -> AnnoTermPar -> AnnoTermPar
| abseq_par: Split -> AnnoTermPar -> AnnoTermPar -> AnnoTermPar
| abpar_par: Loc -> Split -> AnnoTermPar -> Term -> AnnoTermPar.

Fixpoint unannoPar (t:AnnoTermPar) : Term :=
  match t with
  | aasp_par a => asp a
  | aatt_par p t => att p t
  | alseq_par a1 a2 => lseq (unannoPar a1) (unannoPar a2)                 
  | abseq_par spl a1 a2 => bseq spl (unannoPar a1) (unannoPar a2) 
  | abpar_par _ spl a1 a2 => bpar spl (unannoPar a1) a2
  end.

Fixpoint anno_par (t:Term) (loc:Loc) : (Loc * AnnoTermPar)  :=
  match t with
  | asp a => (loc, aasp_par a)
  | att p t => (loc, aatt_par p t)
                     
  | lseq t1 t2 =>
    let '(loc', t1') := anno_par t1 loc in
    let '(loc'', t2') := anno_par t2 loc' in

    (loc'', alseq_par t1' t2')
      
  | bseq spl t1 t2 =>
    let '(loc', t1') := anno_par t1 loc in
    let '(loc'', t2') := anno_par t2 loc' in

    (loc'', abseq_par spl t1' t2')
      
  | bpar spl t1 t2 =>
    let '(loc', t1') := anno_par t1 (S loc) in
    
    (loc', abpar_par loc spl t1' t2)
  end.

Definition annotated_par (x:Term) :=
  snd (anno_par x 0).

Inductive term_sub : Term -> Term -> Prop :=
| termsub_refl_annt: forall t: Term, term_sub t t
| aatt_sub_annt: forall t t' p,
    term_sub t' t ->
    term_sub t' (att p t)
| alseq_subl_annt: forall t' t1 t2,
    term_sub t' t1 ->
    term_sub t' (lseq t1 t2)
| alseq_subr_annt: forall t' t1 t2,
    term_sub t' t2 ->
    term_sub t' (lseq t1 t2)
| abseq_subl_annt: forall t' t1 t2 s,
    term_sub t' t1 ->
    term_sub t' (bseq s t1 t2)
| abseq_subr_annt: forall t' t1 t2 s,
    term_sub t' t2 ->
    term_sub t' (bseq s t1 t2)
| abpar_subl_annt: forall t' t1 t2 s,
    term_sub t' t1 ->
    term_sub t' (bpar s t1 t2)
| abpar_subr_annt: forall t' t1 t2 s,
    term_sub t' t2 ->
    term_sub t' (bpar s t1 t2).
Hint Constructors term_sub : core.

Lemma termsub_transitive: forall t t' t'',
    term_sub t t' ->
    term_sub t' t'' ->
    term_sub t t''.
Proof.  
  generalizeEverythingElse t''.
  induction t'';
    intros H H0; ff.
    (* try (invc H0; eauto). *)
Defined.


(*
(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *) *)

Fixpoint anno (t: Term) (i:nat) : (nat * AnnoTerm) :=
  match t with
  | asp x => (S i, (aasp (i, S i) x))

  | att p x =>
    let '(j,a) := anno x (S i)  in
    (S j, aatt (i, S j) p a)

  | lseq x y =>
    let '(j,a) := anno x i in
    let '(k,bt) := anno y j in
    (k, alseq (i, k) a bt)

  | bseq s x y =>
    let '(j,a) := anno x (S i) in
    let '(k,b) := anno y j in
    (S k, abseq (i, S k) s a b)

  | bpar s x y =>
    let '(j,a) := anno x (S i) in
    let '(k,b) := anno y j in
    (S k, abpar (i, S k) s a b)
  end.

Definition annotated x :=
  snd (anno x 0).

Fixpoint unanno a :=
  match a with
  | aasp _ a => asp a
  | aatt _ p t => att p (unanno t)
  | alseq _ a1 a2 => lseq (unanno a1) (unanno a2)                 
  | abseq _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
  end.

Lemma anno_unanno: forall t i,
    unanno (snd (anno t i)) = t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
  -
    ff.
    erewrite <- IHt.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
Defined.

Lemma anno_unanno_par: forall a l l' annt,
    anno_par a l = (l', annt) ->
    unannoPar annt = a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    congruence.
Defined.


Inductive annoP: AnnoTerm -> Term -> Prop :=
| annoP_c: forall anno_term t,
    (exists n n', anno t n = (n',anno_term)) -> (* anno_term = snd (anno t n)) -> *)
    annoP anno_term t.

Inductive annoP_indexed': AnnoTerm -> Term -> nat -> Prop :=
| annoP_c_i': forall anno_term t n,
    (exists n', anno t n = (n', anno_term)) -> (*anno_term = snd (anno t n) -> *)
    annoP_indexed' anno_term t n.

Inductive annoP_indexed: AnnoTerm -> Term -> nat -> nat ->  Prop :=
| annoP_c_i: forall anno_term t n n',
    (*(exists n', anno t n = (n', anno_term)) -> (*anno_term = snd (anno t n) -> *) *)
    anno t n = (n', anno_term) ->
    annoP_indexed anno_term t n n'.

Inductive anno_parP: AnnoTermPar -> Term -> Prop :=
| anno_parP_c: forall par_term t,
    (exists loc loc', anno_par t loc = (loc', par_term)) -> (*par_term = snd (anno_par t loc)) -> *)
    anno_parP par_term t.

Inductive anno_parPloc: AnnoTermPar -> Term -> Loc -> Prop :=
| anno_parP_cloc: forall par_term t loc,
    (exists loc', anno_par t loc = (loc', par_term)) -> (*par_term = snd (anno_par t loc) -> *)
    anno_parPloc par_term t loc.




(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)

(*
Lemma unique_req_events (t:AnnoTerm) : forall p i i0 p1 p2 q q0 t0 t1,
       events t p (req i  loc p1 q  t0) ->
    not (events t p (req i0 loc p2 q0 t1)).
 *)

(** Eval for annotated terms. *)

Fixpoint aeval t p e :=
  match t with
  | aasp _ x => eval (asp x) p e
  | aatt _ q x => aeval x q e
  | alseq _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ s t1 t2 => ss (aeval t1 p ((splitEv_T_l s e)))
                         (aeval t2 p ((splitEv_T_r s e)))
  | abpar _ s t1 t2 => pp (aeval t1 p ((splitEv_T_l s e)))
                         (aeval t2 p ((splitEv_T_r s e)))
  end.

Lemma eval_aeval:
  forall t p e i,
    eval t p e = aeval (snd (anno t i)) p e.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl;
      try (repeat jkjk; auto;congruence);
      try (repeat jkjk'; auto).
Defined.



Inductive well_formed_r_annt: AnnoTerm -> Prop :=
| wf_asp_r_annt: forall r x,
    snd r = S (fst r) ->
    well_formed_r_annt (aasp r x)
| wf_att_r_annt: forall r p x,
    well_formed_r_annt x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r_annt (aatt r p x)
                  
| wf_lseq_r_annt: forall r x y,
    well_formed_r_annt x -> well_formed_r_annt y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) -> 
    well_formed_r_annt (alseq r x y)               
| wf_bseq_r_annt: forall r s x y,
    well_formed_r_annt x -> well_formed_r_annt y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->  
    well_formed_r_annt (abseq r s x y)              
| wf_bpar_r_annt: forall r s x y,
    well_formed_r_annt x -> well_formed_r_annt y ->  
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    (*fst (range y) > fst (range x) -> *)
    well_formed_r_annt (abpar r s x y).
Hint Constructors well_formed_r_annt : core.

Ltac afa :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat |- _] => pose_new_proof (H H2 H3)
  end.

Ltac afa' :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat |- _] => pose_new_proof (H H2 (S H3))
  end.

Ltac afa'' :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat, H4:nat, H5: AnnoTerm |- _] =>
    pose_new_proof (H H2 (H3)(H4) H5)
  end.

Ltac same_index :=
  match goal with
  | [H: anno ?t _ = (?n, _),
        H': anno ?t _ = (?n', _) |- _] =>
    assert_new_proof_by (n = n') eauto
  end.

Lemma same_anno_range: forall t i a b n n',
    anno t i = (n,a) ->
    anno t i = (n',b) ->
    n = n'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try destruct a;
    ff.
Defined.
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm),
  anno t i = (j,t') ->
  j > i.
Proof.
  induction t; intros; (*i j t' ls b H; *)
    ff;
    repeat find_apply_hyp_hyp;
    lia.
Defined.
Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j t',
     anno x i = (j,t') ->
    range (t') = (i, j).
Proof.
  induction x; intros; ff.
Defined.

Ltac haha :=
  let asdff := eapply anno_mono; eauto in
  match goal with
  | [H: anno _ ?x = (?y,_) |- _] => assert_new_proof_by (y > x) (asdff)
  end.

Ltac hehe :=
  match goal with
  | [H: anno ?x ?y = (_,_) |- _] => pose_new_proof (anno_range x y)
  end.

Ltac hehe' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x (S y))
  end.

Ltac hehe'' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x y)
  end.

Ltac do_list_empty :=
  match goal with
    [H: length ?ls = 0 |- _] =>
    assert_new_proof_by (ls = []) ltac:(destruct ls; solve_by_inversion)
  end.

Lemma anno_well_formed_r:
  forall t i j t',
    anno t i = (j, t') ->
    well_formed_r_annt t'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.
  -
    ff.
    +
      econstructor.
      eauto.
      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      assert (n > S i) by (eapply anno_mono; eauto).
      lia.
  -
    ff.
    econstructor.
    eauto.
    eauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.
      
  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      erewrite anno_range.
      2: {
        eassumption.
      }
      
      tauto.
      
      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.     
Defined.
