(*
Experiments in stating "disclosure" properties of the CVM.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Term LTS Cvm_Impl Cvm_St Trace Main ConcreteEvidence.

Require Import CvmSemantics Appraisal_Evidence Eqb_Evidence Auto AbstractedTypes EqClass Helpers_CvmSemantics Disclose_Gen External_Facts Axioms_Io.

Require Import StructTactics.

Require Import ErrorStMonad_Coq.

Require Import Coq.Program.Tactics PeanoNat Lia.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.



Fixpoint evsubt_bool (e:Evidence) (e':Evidence): bool :=
  match (eqb_evidence e e') with
  | true => true
  | false =>
    match e' with
    | uu _ _ _ et' => evsubt_bool e et'
    | ss e1 e2 => evsubt_bool e e1 || evsubt_bool e e2 
    | _ => false
    end
  end.

Lemma eqb_asp_params_refl: forall a,
    eqb_asp_params a a = true.
Proof.
  intros. apply eqb_eq_asp_params. auto.
Qed.

Lemma eqb_evidence_refl: forall e,
    eqb_evidence e e = true.
Proof.
  intros. apply eqb_eq_evidence. auto.
Qed.

Lemma eqb_plc_refl `{H : EqClass ID_Type} : forall (p:Plc),
    eqb_plc p p = true.
Proof.
  intros. apply eqb_eq_plc. auto.
Qed.

Lemma eqb_fwd_refl : forall (f:FWD),
    eqb_fwd f f = true.
Proof.
  intros. apply eqb_eq_fwd. auto.
Qed.

Lemma evsubt_prop_bool: forall e e',
    EvSubT e e' -> evsubt_bool e e' = true.
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    try (invc H; ff; try tauto; rewrite PeanoNat.Nat.eqb_refl; tauto).
  - (* uu case *)
    invc H.
    +
      ff.
      (*
    rewrite PeanoNat.Nat.eqb_refl. *)
    rewrite eqb_asp_params_refl.
    rewrite eqb_evidence_refl.
    rewrite eqb_plc_refl.
    rewrite eqb_fwd_refl.
    ff.
    
    +
      ff.
      assert (evsubt_bool e e' = true) by eauto.
      rewrite H.
      ff.
      
  - (* ss case *)
    ff.
    invc H.
    +
      rewrite eqb_evidence_refl.
      ff.
    +
      erewrite IHe'1.
      ff.
      eassumption.
    +
      erewrite IHe'2.
      ff.
      rewrite Bool.orb_true_r.
      ff.
      eassumption.
Qed.


Lemma evsubt_bool_prop: forall e e',
    evsubt_bool e e' = true -> EvSubT e e'.
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros.
  -
    ff.
    destruct e; ff.
  -
    ff.
    destruct e; ff.
    rewrite Nat.eqb_eq in *.
    ff.
  - (* uu case *)
    ff.
    destruct e; ff.
    rewrite Bool.andb_true_iff in Heqb.
    rewrite Bool.andb_true_iff in Heqb.
    destruct_conjs.
    rewrite eqb_eq_asp_params in *.
    rewrite Bool.andb_true_iff in H0.
    invc H0.
    apply eqb_eq_plc in H3.
    apply eqb_eq_fwd in H4.
    apply eqb_eq_evidence in H1.
    subst.
    eapply evsub_reflT.
    
  - (* ss case *)
    ff.

     assert (
        (orb (eqb_evidence e (ss e'1 e'2))%bool
            (evsubt_bool e e'1 || evsubt_bool e e'2)) =
    (if eqb_evidence e (ss e'1 e'2)
       then true
     else (evsubt_bool e e'1 || evsubt_bool e e'2)%bool)).
     {
       apply Bool.orb_lazy_alt.
     }
     rewrite H in H0.

     apply Bool.orb_prop in H0.
     invc H0.
    +
      ff.
      apply eqb_eq_evidence in Heqb.
      ff.
    +
      apply Bool.orb_prop in H1.
      invc H1.
      ++
        ff.
      ++
        ff.
Qed.

Lemma evsubt_bool_prop_iff: forall e e',
    EvSubT e e' <-> evsubt_bool e e' = true.
Proof.
  intros; split.
  apply evsubt_prop_bool.
  apply evsubt_bool_prop.
Qed.
  




(* A relation specifying events (Ev) that disclose evidence to other places.
   Technically, we are considering "Evidence Types" (Evidence), but the correspondence of 
   those types to concrete binary evidence values is maintained by the CVM.
 
  Example:  
  discloses_to_remote ev (q,et) says that event ev discloses evidence of type et to place q.

*)

Inductive discloses_to_remote: Ev -> (Plc*Evidence) -> Prop :=
| at_disclose: forall i p q t e (*e'*),
    (* EvSubT e' e -> *)
    discloses_to_remote (req i p q t e) (q,e).

Definition discloses_aspid_to_remote (q:Plc) (i:ASP_ID): Prop :=
  let gen_aspid_evidence := (specific_aspid_genEvidence i) in
  forall et reqid p t e,
    ((evidence_matches_gen gen_aspid_evidence et) = true) /\
    EvSubT et e ->
    (discloses_to_remote (req reqid p q t e) (q, et)).
                                                          



(*

Inductive discloses_to_asp: Ev -> (Plc*ASP_ID*Evidence) -> Prop :=
| asp_disclose: forall i p (asp_id:ASP_ID) args tpl tid e e',
    EvSubT e' e ->
    discloses_to_asp
      (umeas i p (asp_paramsC asp_id args tpl tid) e)
      (p,asp_id,e').
*)


(*
Inductive discloses_to_asp: Ev -> (Plc*ASP_ID*Evidence) -> Prop :=
| asp_disclose: forall i p ps (asp_id:ASP_ID) e,
    let asp_id := get_aspid ps in
    ps <> sig_params ->
    ps <> hsh_params ->
    discloses_to_asp
      (umeas i p ps e)
      (p,asp_id,e).
*)

Definition splitEv_mt (sp:SP) (e:Evidence) : Evidence :=
  match sp with
  | ALL => e
  | NONE => mt
  end.

Fixpoint term_discloses_to_remote (t:Term) (p:Plc) (e:Evidence) (r:(Plc*Evidence)) : bool :=
  match t with
  | att q t' => (eqb_plc q (fst r)) && (eqb_evidence (snd r) e)(* (evsubt_bool (snd r) e) *) ||
               (term_discloses_to_remote t' q e r)
  | lseq t1 t2 => (term_discloses_to_remote t1 p e r) ||
                 (term_discloses_to_remote t2 p (eval t1 p e) r)
  | bseq (sp1,sp2) t1 t2 => (term_discloses_to_remote t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_remote t2 p (splitEv_mt sp2 e) r)
  | bpar (sp1,sp2) t1 t2 => (term_discloses_to_remote t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_remote t2 p (splitEv_mt sp2 e) r)
  | _ => false
  end.


(*
Definition discloses_aspid_to_remote (q:Plc) (i:ASP_ID): Prop :=
  let gen_aspid_evidence := (specific_aspid_genEvidence i) in
  forall et i p t e,
    ((evidence_matches_gen gen_aspid_evidence et) = true) /\
    (discloses_to_remote (req i p q t e) (q, et)).
 *)

Definition term_discloses_aspid_to_remote (t:Term) (p:Plc) (e:Evidence) (i:ASP_ID) (r:Plc) : Prop :=
  let gen_aspid_evidence := (specific_aspid_genEvidence i) in
  exists et e',
    ((evidence_matches_gen gen_aspid_evidence et) = true) /\
    EvSubT et e' /\
    ((term_discloses_to_remote t p e (r,e')) = true).



(*
Inductive discloses_to_remote: Ev -> (Plc*Evidence) -> Prop :=
| at_disclose: forall i p q t e e',
    EvSubT e' e ->
    discloses_to_remote (req i p q t e) (q,e').
*)

Definition cvm_trace_discloses_to_remote (tr:list Ev) (r:Plc) (e:Evidence) : Prop :=
  (* let gen_aspid_evidence := (specific_aspid_genEvidence i) in *)
  exists ev reqi p t (*e et*),
    (In ev tr) /\
    ev = (req reqi p r t e).

           (*
    /\
    (evidence_matches_gen gen_aspid_evidence et = true) /\
    evsubt_bool et e = true. *)

Definition cvm_trace_discloses_aspid_to_remote (tr:list Ev) (i:ASP_ID) (r:Plc) : Prop :=
  let gen_aspid_evidence := (specific_aspid_genEvidence i) in
  exists e et,
     (evidence_matches_gen gen_aspid_evidence et = true) /\
     evsubt_bool et e = true /\
     cvm_trace_discloses_to_remote tr r e.

(*
  exists ev reqi p t e et,
    (In ev tr) /\
    ev = (req reqi p r t e) /\
    (evidence_matches_gen gen_aspid_evidence et = true) /\
    evsubt_bool et e = true.
 *)

Definition events_discloses (annt:AnnoTerm) (p:Plc) (e:Evidence) (* (i:ASP_ID) *) (r:Plc) (e':Evidence): Prop :=
  (*forall annt cvmi,
    annoP_indexed annt t 0 cvmi-> *)
    (* let gen_aspid_evidence := (specific_aspid_genEvidence i) in *)
    exists ev reqi reqp reqt (*reqe et*) (*p*),
      (
        (* annoP annt t /\  *)
        events annt p e ev /\
        ev = (req reqi reqp r reqt e')

        (* /\
        (evidence_matches_gen gen_aspid_evidence et = true) /\
        evsubt_bool et reqe = true *)
      ).


Definition events_discloses_aspid (annt:AnnoTerm) (p:Plc) (e:Evidence) (i:ASP_ID) (r:Plc): Prop :=
  (*forall annt cvmi,
    annoP_indexed annt t 0 cvmi-> *)
  let gen_aspid_evidence := (specific_aspid_genEvidence i) in
  exists et reqe,
     (evidence_matches_gen gen_aspid_evidence et = true) /\
     evsubt_bool et reqe = true /\
     events_discloses annt p e r reqe.
    
(*
    exists ev reqi reqp reqt reqe et (*p*),
      (
        (* annoP annt t /\  *)
        events annt p e ev /\
        ev = (req reqi reqp r reqt reqe) /\
        (evidence_matches_gen gen_aspid_evidence et = true) /\
        evsubt_bool et reqe = true
      ).
*)

Lemma term_disc_remote: forall t p e i r p0,
          term_discloses_aspid_to_remote t p e i r ->
          term_discloses_aspid_to_remote <{ @ p [t] }> p0 e i r.
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  exists H0.
  split.
  -
    eassumption.
  -
    simpl in *.
    destruct x; try solve_by_inversion.
    destruct a; try solve_by_inversion.
    assert (a = i).
    {
      assert (eqb a i = true).
      {
        repeat rewrite Bool.andb_true_r in H.
        auto.
      }
      eapply eqb_eq_aspid; eauto.
    }
    
    subst.
    find_rewrite.
    rewrite Bool.orb_true_r.
    auto.
Qed.

Lemma term_disc_lseq_l: forall t1 t2 p e i r,
          term_discloses_aspid_to_remote t1 p e i r ->
          term_discloses_aspid_to_remote <{ t1 -> t2 }> p e i r.
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  exists H0.
  split.
  -
    eassumption.
  -
    simpl in *.
    destruct x; try solve_by_inversion.
    destruct a; try solve_by_inversion.
    assert (a = i).
    {
      assert (eqb a i = true).
      {
        repeat rewrite Bool.andb_true_r in H.
        auto.
      }
      eapply eqb_eq_aspid; eauto.
    }
    
    subst.
    find_rewrite.
    rewrite Bool.orb_true_l.
    auto.
Qed.

Lemma term_disc_lseq_r: forall t1 t2 p e i r,
          term_discloses_aspid_to_remote t2 p (eval t1 p e) i r ->
          term_discloses_aspid_to_remote <{ t1 -> t2 }> p e i r.

(*
  H8 : term_discloses_aspid_to_remote t2 p (aeval a H7 e) i r
  ============================
  term_discloses_aspid_to_remote <{ t1 -> t2 }> p e i r
*)
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  exists H0.
  split.
  -
    eassumption.
  -
    simpl in *.
    destruct x; try solve_by_inversion.
    destruct a; try solve_by_inversion.
    assert (a = i).
    {
      assert (eqb a i = true).
      {
        repeat rewrite Bool.andb_true_r in H.
        auto.
      }
      eapply eqb_eq_aspid; eauto.
    }
    
    subst.
    find_rewrite.
    rewrite Bool.orb_true_r.
    auto.
Qed.

Lemma term_disc_bseq_l: forall t1 t2 p e i r s,
          term_discloses_aspid_to_remote t1 p (splitEv_T_l s e) i r ->
          term_discloses_aspid_to_remote (bseq s t1 t2) p e i r.
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  exists H0.
  split.
  -
    eassumption.
  -
    simpl in *.
    destruct x; try solve_by_inversion.
    destruct a; try solve_by_inversion.
    assert (a = i).
    {
      assert (eqb a i = true).
      {
        repeat rewrite Bool.andb_true_r in H.
        auto.
      }
      eapply eqb_eq_aspid; eauto.
    }
    
    subst.
    destruct s.
    destruct s;
      
      simpl in *;
      rewrite H2;
      
      rewrite Bool.orb_true_l;
      auto.
Qed.

Lemma term_disc_bseq_r: forall t1 t2 p e i r s,
          term_discloses_aspid_to_remote t2 p (splitEv_T_r s e) i r ->
          term_discloses_aspid_to_remote (bseq s t1 t2) p e i r.
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  exists H0.
  split.
  -
    eassumption.
  -
    simpl in *.
    destruct x; try solve_by_inversion.
    destruct a; try solve_by_inversion.
    assert (a = i).
    {
      assert (eqb a i = true).
      {
        repeat rewrite Bool.andb_true_r in H.
        auto.
      }
      eapply eqb_eq_aspid; eauto.
    }
    
    subst.
    destruct s;
      destruct s;
      destruct s0;

      simpl in *;
      rewrite H2;
      
      rewrite Bool.orb_true_r;
      auto.
Qed.

Lemma term_disc_bpar_l: forall t1 t2 p e i r s,
          term_discloses_aspid_to_remote t1 p (splitEv_T_l s e) i r ->
          term_discloses_aspid_to_remote (bpar s t1 t2) p e i r.
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  exists H0.
  split.
  -
    eassumption.
  -
    simpl in *.
    destruct x; try solve_by_inversion.
    destruct a; try solve_by_inversion.
    assert (a = i).
    {
      assert (eqb a i = true).
      {
        repeat rewrite Bool.andb_true_r in H.
        auto.
      }
      eapply eqb_eq_aspid; eauto.
    }
    
    subst.
    destruct s;
      destruct s;
      destruct s0;

      simpl in *;
      rewrite H2;
      
      rewrite Bool.orb_true_l;
      auto.
Qed.

Lemma term_disc_bpar_r: forall t1 t2 p e i r s,
          term_discloses_aspid_to_remote t2 p (splitEv_T_r s e) i r ->
          term_discloses_aspid_to_remote (bpar s t1 t2) p e i r.
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  exists H0.
  split.
  -
    eassumption.
  -
    simpl in *.
    destruct x; try solve_by_inversion.
    destruct a; try solve_by_inversion.
    assert (a = i).
    {
      assert (eqb a i = true).
      {
        repeat rewrite Bool.andb_true_r in H.
        auto.
      }
      eapply eqb_eq_aspid; eauto.
    }
    
    subst.
    destruct s;
      destruct s;
      destruct s0;

      simpl in *;
      rewrite H2;
      
      rewrite Bool.orb_true_r;
      auto.
Qed.

Lemma term_discloses_respects_events : forall annt t p e r H2,
      annoP annt t -> 
      events_discloses annt p e r H2 ->
      term_discloses_to_remote t p e (r, H2) = true.
Proof.
  intros.
  unfold not in * ; intros.
  unfold events_discloses_aspid in *.
  (*
  assert (exists annt cvmi, annoP_indexed annt t 0 cvmi). admit.
  destruct_conjs.
  specialize (H0 H1 H2 H3). *)
  destruct_conjs.
  subst.

  generalizeEverythingElse t.
  induction t; intros.

  - (* asp case *)
    invc H.
    destruct_conjs.
    invc H0.
    destruct_conjs.
    repeat ff.
  - (* at case *)
    invc H0.
    destruct_conjs.
    ff.
    invc H.
    destruct_conjs.

    invc H5; try solve_by_inversion.
    ff.
    invc H4.
    +
       assert (eqb_plc r r = true).
    {
      eapply eqb_eq_plc; eauto.
    }
        assert (eqb_evidence H2 H2 = true).
    {
      eapply eqb_evidence_refl.
    }

    find_rewrite.
    find_rewrite.
    simpl.
    tauto.
    +
      assert (term_discloses_to_remote t p e (r, H2) = true).
      {
        eapply IHt with (p:=p).
        econstructor.
        repeat eexists.
        eassumption.
        econstructor.
        repeat eexists.
        eassumption.
      }
      find_rewrite.
      rewrite Bool.orb_true_r.
      auto.
  

  - (* lseq case *)

    invc H.
    destruct_conjs.

    invc H3.
    repeat break_let.
    ff.

    invc H0.
    destruct_conjs.
    subst.
    invc H5.
    +

      assert (term_discloses_to_remote t1 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      
    + (* right subterm *)

      assert (term_discloses_to_remote t2 p (eval t1 p e) (r, H2) = true).
      {
         assert (aeval a p e = eval t1 p e).
      {
        erewrite eval_aeval.
        rewrite Heqp0.
        simpl.
        tauto.
      }
      rewrite <- H5.
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.

      rewrite Bool.orb_true_r.
      tauto.

  - (* bseq case *)

    invc H.
    destruct_conjs.

    invc H3.
    repeat break_let.
    ff.

    invc H0.
    destruct_conjs.
    subst.
    destruct s0; destruct s1; ff.


    +
      
      
      
      invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
    +
            invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
    +
            invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
    +
            invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
  - (* bpar case *)
        invc H.
    destruct_conjs.

    invc H3.
    repeat break_let.
    ff.

    invc H0.
    destruct_conjs.
    subst.
    destruct s0; destruct s1; ff.


    +
      
      
      
      invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
    +
            invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
    +
            invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p e (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
    +
            invc H4.
      ++
    

      assert (term_discloses_to_remote t1 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
      simpl.
      tauto.
      ++
          assert (term_discloses_to_remote t2 p mt (r, H2) = true).
      {

      (* left subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.
      ff.
      econstructor.
      repeat eexists.
      eassumption.
      }
      find_rewrite.
         rewrite Bool.orb_true_r.
         tauto.
Qed.


Lemma fdfdfd: forall Q P: Prop,
    (P -> Q) ->
    (~Q -> ~P).
Proof.
  intros.
  unfold not in *.
  intros.
  apply H0. apply H. eassumption.
Qed.

Lemma events_respects_term_disclosure: forall t p q e r annt,
    annoP annt t -> 

  (~ (term_discloses_to_remote t p e (q,r) = true)) ->

  ~ (events_discloses annt p e q r).
Proof.
  intros t p q e r annt H.
  apply fdfdfd.
  intros.
  eapply term_discloses_respects_events; eauto.
Qed.


Lemma events_respects_term_disclosure_aspid: forall t p e i r annt,
    annoP annt t -> 

  ~ (term_discloses_aspid_to_remote t p e i r) ->

  ~ (events_discloses_aspid annt p e i r).
Proof.
  intros.
  unfold term_discloses_aspid_to_remote in *.
  unfold events_discloses_aspid in *.
  unfold not in H0.
  unfold not in *.
  intros.
  apply H0.
  destruct_conjs.
  exists H1. exists H2.
  split; try eassumption.
  split.
  rewrite evsubt_bool_prop_iff.
  eassumption.

  eapply term_discloses_respects_events; eauto.
Qed.


(*


  destruct_conjs.

  intros.
  unfold not in * ; intros.
  unfold events_discloses_aspid in *.
  (*
  assert (exists annt cvmi, annoP_indexed annt t 0 cvmi). admit.
  destruct_conjs.
  specialize (H0 H1 H2 H3). *)
  destruct_conjs.
  subst.

  generalizeEverythingElse t.
  induction t; intros.

  - (* asp case *)
    invc H.
    destruct_conjs.
    repeat ff.
  - (* at case *)

  eapply H0.
  unfold term_discloses_aspid_to_remote.
  exists H6.
  split.
  eassumption.
  simpl.

  (*
  invc H3.
  destruct_conjs.
  assert (exists rng t', H1 = aatt rng p t'). admit.
  invc H0.
  destruct_conjs.
  subst. *)
  invc H.
  destruct_conjs.
  invc H8.
  break_let.
  inversion H12.
  subst.
  clear H12.
  invc H7.
  +
    assert (eqb_plc r r = true).
    {
      eapply eqb_eq_plc; eauto.
    }

    find_rewrite.
    find_rewrite.
    simpl.
    tauto.

  +
    (*
    rewrite <- Heqe0 in *. clear Heqe0.
    subst. *)
    assert (term_discloses_to_remote t p e (r, H6) = true).
    {
      assert False.
      {
        eapply IHt with (p:=p).
        econstructor.
        repeat eexists.
        eassumption.




        (*
        admit. (* TODO: use recursive at hyp (H) *)
         *)
        Focus 3.
        eassumption.
        Focus 3.
        eassumption.
        Focus 2.
        eassumption.

        intros.
        apply H0.



        apply term_disc_remote. eassumption.


        
        (*
        Focus 2.
        eassumption.
        invc Heqp1.
        econstructor.
        repeat eexists.
        eauto. *)
      }
      
(*
        eassumption.
        invc H3; repeat ff.
        econstructor.
        eexists. eexists.
        apply Heqp1.
        eassumption.
 } *)
      solve_by_inversion.
    }
    find_rewrite.
    rewrite Bool.orb_true_r.
    auto.

  (*


  
  assert (exists t', H1 = att p t'). admit.
  destruct_conjs.
  subst.
  simpl.
  admit.
   *)
  

  - (* lseq case *)

    invc H.
    destruct_conjs.

    invc H8.
    repeat break_let.
    invc H12.

    invc H7.
    + (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      Focus 2.
      eassumption.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      intros.
      apply H0.

      apply term_disc_lseq_l.
      eassumption.

      (*
      econstructor.
      repeat eexists.
      eassumption. *)
    +
       (* right subterm *)
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      Focus 2.
      eassumption.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      intros.
      apply H0.

      apply term_disc_lseq_r.
      assert (aeval a p e = eval t1 p e).
      {
        erewrite eval_aeval.
        rewrite Heqp0.
        simpl.
        tauto.
      }
      rewrite <- H8.
      
      eassumption.
      
      (*
      econstructor.
      repeat eexists.
      eassumption. *)
      
  - (* bseq case *)
     invc H.
     destruct_conjs.

     invc H8.
     repeat break_let.
     invc H12.

    invc H7.
    + (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      Focus 2.
      eassumption.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      intros.
      apply H0.

      apply term_disc_bseq_l.
      (*
      assert (aeval a p e = eval t1 p e).
      {
        admit.
      }
      rewrite <- H8. *)
      
      eassumption.

      (*
      econstructor.
      repeat eexists.
      eassumption. *)
    +
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      Focus 2.
      eassumption.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      intros.
      apply H0.

      apply term_disc_bseq_r.
      (*
      assert (aeval a p e = eval t1 p e).
      {
        admit.
      }
      rewrite <- H8. *)
      
      eassumption.

      (*
      econstructor.
      repeat eexists.
      eassumption. *)

  - (* bpar case *)
    invc H.
     destruct_conjs.

     invc H8.
     repeat break_let.
     invc H12.

    invc H7.
    + (* left subterm *)
      eapply IHt1 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      Focus 2.
      eassumption.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      intros.
      apply H0.

      apply term_disc_bpar_l. (* TODO: weird that "apply term_disc_bseq_l" works here just as well...must be evaluation happening inline *)
      (*
      assert (aeval a p e = eval t1 p e).
      {
        admit.
      }
      rewrite <- H8. *)
      
      eassumption.

      (*
      econstructor.
      repeat eexists.
      eassumption. *)
    +
      eapply IHt2 with (p:=p). (* with (H7 := (uu p0 f (asp_paramsC a0 l p1 t) e0)). *)
      econstructor.
      repeat eexists.
      eassumption.

      Focus 2.
      eassumption.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      intros.
      apply H0.

      apply term_disc_bpar_r. (* TODO: weird that "apply term_disc_bseq_r" works here just as well...must be evaluation happening inline *)
      (*
      assert (aeval a p e = eval t1 p e).
      {
        admit.
      }
      rewrite <- H8. *)
      
      eassumption.
Qed.

*)

Lemma cvm_implies_events: forall t annt e e' bits bits' p p' cvmi cvmi' cvm_tr ev ac ac',
    annoP_indexed annt t cvmi cvmi'->

    build_cvmP (copland_compile t)
         {| st_ev := evc bits e; st_trace := []; st_pl := p; st_evid := cvmi; st_AM_config := ac |} 
         (resultC tt) {| st_ev := evc bits' e'; st_trace := cvm_tr; st_pl := p'; st_evid := cvmi'; st_AM_config := ac' |} ->

    In ev cvm_tr ->

    events annt p e ev.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
    wrap_ccp_anno;
    repeat Auto.ff;
    destruct a; invc H; repeat Auto.ff;
      wrap_ccp_anno;
      repeat Auto.ff;
      try destruct s; wrap_ccp_anno;
      try destruct f;
      try destruct H1;
      subst;
      try solve_by_inversion;
    
      try (econstructor; econstructor; reflexivity).
  -
    wrap_ccp_anno.
    repeat ff.

    assert (n = cvmi + event_id_span' t + 1) by lia.
    subst.
    clear H6.
   
    assert (t = unanno a) as H11.
    {
      invc Heqp1.
      
      erewrite <- anno_unanno at 1.
      rewrite H0.
      tauto.
    }


    door.
    +
      rewrite <- H0.
      rewrite H11.
      apply evtsattreq.
      auto.
    +
      assert ( (In ev (cvm_events t p e)) \/
               ev = (rpy (cvmi + 1 + event_id_span' t) p' p (eval t p e)
                         (* (get_et (IO_Stubs.doRemote_session t p (evc bits e))) *) )
             ).
      {

        apply in_app_or in H0.
        door.
        +
          left; eauto.
        +
          right.
          invc H0;
            try auto;
            try solve_by_inversion.
      }
      
      door.

      assert (
              build_cvm (copland_compile t)
                    {| st_ev := (evc bits e);
                       st_trace := [];
                       st_pl := p;
                       st_evid := (S cvmi); st_AM_config := ac' |} =
    (resultC tt,
     {| st_ev := cvm_evidence_core (copland_compile t) p (evc bits e);
        st_trace := cvm_events_core (copland_compile t) p (get_et (evc bits e));
        st_pl := p;
        st_evid := ( (S cvmi) + event_id_span (copland_compile t));
        st_AM_config := ac'
     |})).
      apply build_cvm_external.

      destruct (cvm_evidence_core (copland_compile t) p (evc bits e)).
      unfold cvm_events in *.


      
      econstructor.

      eapply IHt; [ | simpl in *; econstructor; eauto | eauto ].
      2: {
        subst; rewrite eval_aeval'; apply evtsattrpy;
        simpl; lia.
      }
      econstructor.

      invc Heqp1.
      repeat ff.
      rewrite <- event_id_spans_same.
      simpl in *.
      assert (S (cvmi + event_id_span' (unanno a)) =
              cvmi + event_id_span' (unanno a) + 1) by lia.
      rewrite H4.
      eassumption.
  - (* alseq case *)
    invc H.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    fold copland_compile in *.

    inversion H2.
    subst.
    ff.
    do_anno_indexed_redo.
    do_anno_indexed_redo.
    
    assert (n = H4).
    {
      eapply cvm_spans_annoTerm; eauto;
      econstructor; eauto.
    }
    subst.

    
    destruct x.
     

    assert (In ev H \/ In ev H7).
    {
      apply in_app_or in H1.
        door.
        +
          left; eauto.
        +
          right.
          invc H0;
            try auto;
            try solve_by_inversion.
    }

    door.
    +
      apply evtslseql.
      eapply IHt1.
      econstructor.
      eassumption.
      eassumption.
      eassumption.
    +

      

    assert (e0 = aeval a p e).
      {
      rewrite <- eval_aeval'.
      assert (t1 = unanno a).
    {
      symmetry.
      invc Heqp1.
      erewrite <- anno_unanno.
      rewrite Heqp2.
      tauto.
    }
    eapply cvm_refines_lts_evidence.
    econstructor; eauto.
    rewrite <- H9.
    eassumption.
      }
      rewrite H9 in H8.
      

      assert (p = H3).
      {
        invc H6.
        do_pl_immut.
        congruence.
      }
      

      
      invc Heqp3.
      apply evtslseqr.
      eapply IHt2.
      econstructor.
      eassumption.
      eassumption.
      eassumption.
  - (* abseq case *)
    wrap_ccp_anno;
    repeat Auto.ff;
    wrap_ccp_anno;
    repeat Auto.ff.
    +

    assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply cvm_spans_annoTerm.
      eassumption.
      econstructor; tauto.
      invc Heqp0.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
    {
      apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }

    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.

    +
          assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply cvm_spans_annoTerm.
      eassumption.
      econstructor; tauto.
      invc Heqp0.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
    {
            apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }
    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.

    +
          assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply cvm_spans_annoTerm.
      eassumption.
      econstructor; tauto.
      invc Heqp0.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
    {
            apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }
    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.

    +
          assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply cvm_spans_annoTerm.
      eassumption.
      econstructor; tauto.
      invc Heqp0.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
    {
            apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }
    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.


  - (* abpar case *)

    wrap_ccp_anno;
    Auto.ff;
    wrap_ccp_anno;
    Auto.ff.

    +

    assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply cvm_spans_annoTerm; eauto.
      
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (copland_compile t2) e] ++
                   blah ++ [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p).
    {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (copland_compile t2) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (copland_compile t2) e)] ++ blah ++
                                                               [cvm_thread_end 0]))).
      {
        simpl.
        tauto.
      }
      rewrite H1 in H0.

        apply in_app_or in H0.
        door.
      ++
        invc H0; try eauto; try solve_by_inversion.
      ++
        eauto.

      + invc H0; try eauto; try solve_by_inversion.
    }


    door.
    subst.

    apply evtsbparsplit.
    auto.
    door.
    rewrite thread_bookend_peel in H0.

    admit. (* TODO: axiom? *)
    eauto.


    subst.

    apply evtsbparjoin.
    simpl.
    lia.


    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply cvm_spans_annoTerm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.


    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah ++
                   [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p
           ).
    {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e)] ++ blah ++
                                                               [cvm_thread_end 0]))).
      {
        simpl.
        tauto.
      }
      rewrite H1 in H0.

        apply in_app_or in H0.
        door.
      ++
        invc H0; try eauto; try solve_by_inversion.
      ++
        eauto.

      + invc H0; try eauto; try solve_by_inversion.
    }
  
    door.
    subst.

    apply evtsbparsplit.
    auto.
    door.
    rewrite thread_bookend_peel in H0; eauto.
    
    admit. (* TODO: axiom? *)


    subst.

    apply evtsbparjoin.
    simpl.
    lia.

    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply cvm_spans_annoTerm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (copland_compile t2) e] ++
                   blah ++ [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p).
        {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (copland_compile t2) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (copland_compile t2) e)] ++ blah ++
                                                               [cvm_thread_end 0]))).
      {
        simpl.
        tauto.
      }
      rewrite H1 in H0.

        apply in_app_or in H0.
        door.
      ++
        invc H0; try eauto; try solve_by_inversion.
      ++
        eauto.

      + invc H0; try eauto; try solve_by_inversion.
    }

    door.
    subst.

    apply evtsbparsplit.
    auto.
    door.
    rewrite thread_bookend_peel in H0.

    admit. (* TODO: axiom? *)
    eauto.


    subst.

    apply evtsbparjoin.
    simpl.
    lia.

    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply cvm_spans_annoTerm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah ++
                   [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p
           ).
        {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e)] ++ blah ++
                                                               [cvm_thread_end 0]))).
      {
        simpl.
        tauto.
      }
      rewrite H1 in H0.

        apply in_app_or in H0.
        door.
      ++
        invc H0; try eauto; try solve_by_inversion.
      ++
        eauto.

      + invc H0; try eauto; try solve_by_inversion.
    }

    door.
    subst.

    apply evtsbparsplit.
    auto.
    door.
    rewrite thread_bookend_peel in H0.

    assert (In ev blah \/
            In ev (cvm_events_core (copland_compile t2) p mt)).
    admit. (* TODO: axiom here? *)
    door.

    apply evtsbparl.

    simpl in *.
    unfold mt_evc in *.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H4 in *.

    eapply IHt1.
    eassumption.
    eapply restl.
    (* 
    assert ((Term_Defs.split cvmi p :: cvm_thread_start 0 p <<core>{ CLR -> (copland_compile t2) }> e :: blah) = 
    ([Term_Defs.split cvmi p :: cvm_thread_start 0 p <<core>{ CLR -> (copland_compile t2) }> e] ++ blah)).
    {
      intuition.
    }
    *)
    admit.
    eassumption.


    apply evtsbparr.
    simpl.

    

    admit. (* TODO:  axiom here? *)
    eauto.


    subst.

    apply evtsbparjoin.
    simpl.
    lia.

Admitted.


Lemma cvm_respects_events_disclosure_aspid:
  forall t p e i r atp bits bits' p' e' cvm_tr cvmi cvmi' annt ac ac',
    
    annoP_indexed annt t cvmi cvmi' ->
    ~ (events_discloses_aspid annt p e i r) ->
    
    term_to_coreP t atp ->
    build_cvmP atp
               (mk_st (evc bits e) [] p cvmi ac)
               (resultC tt)
               (mk_st (evc bits' e') cvm_tr p' cvmi' ac') ->

    ~ (cvm_trace_discloses_aspid_to_remote cvm_tr i r).

Proof.
  unfold not in *; intros.
  apply H0.
  invc H3.
  destruct_conjs.
  unfold events_discloses_aspid.
  exists H4. exists x. (* exists H3. exists H5. exists H6. exists H7. *)
  split.
  invc H1.
  eassumption.

  split.
  eassumption.

  invc H6.
  destruct_conjs.

  econstructor.
  exists H7. exists H6. exists H8.
  split.
  2: { 
    reflexivity.
  }
  invc H1.
  eapply cvm_implies_events; eauto.
Qed.

Lemma can_annoP : forall t,
    exists annt, annoP annt t.
Proof.
Admitted.

Lemma can_annoP_indexed: forall t atp bits bits' e e' p p' cvm_tr cvmi cvmi' ac ac',
term_to_coreP t atp ->
build_cvmP atp {| st_ev := evc bits e; st_trace := []; st_pl := p; st_evid := cvmi; st_AM_config := ac |}
          (resultC tt) {| st_ev := evc bits' e'; st_trace := cvm_tr; st_pl := p'; st_evid := cvmi'; st_AM_config := ac' |} ->
exists annt,
  annoP_indexed annt t cvmi cvmi'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; repeat Auto.ff.
  -
    destruct a; invc H; invc H0; repeat Auto.ff;
    eexists; econstructor; simpl;
    assert (S cvmi = cvmi + 1) by lia;
    find_rewrite; reflexivity.
  -
    invc H0; ff.
    invc H; ff.


    eexists.
    econstructor.
    ff.
    assert (S n = cvmi + 1 + event_id_span' t + 1).
    {
      admit.
    }
    find_rewrite.
Abort.


Lemma cvm_respects_term_disclosure_aspid:
  forall t p e i r atp bits bits' p' e' cvm_tr cvmi cvmi' annt ac ac',

    annoP_indexed annt t cvmi cvmi' ->

  ~ (term_discloses_aspid_to_remote t p e i r) ->
  
  term_to_coreP t atp ->
  build_cvmP atp
             (mk_st (evc bits e) [] p cvmi ac)
             (resultC tt)
             (mk_st (evc bits' e') cvm_tr p' cvmi' ac') ->

  ~ (cvm_trace_discloses_aspid_to_remote cvm_tr i r).
Proof.
  intros.
  (*
  assert (exists annt, annoP_indexed annt t cvmi cvmi').
  {
    eapply can_annoP_indexed; eauto.
  }
  destruct_conjs.
   *)
  
  eapply cvm_respects_events_disclosure_aspid.
  eassumption.
  eapply events_respects_term_disclosure_aspid.
  invc H.
  econstructor.
  repeat eexists.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
Qed.



(*
Lemma filter_remote_disclosures_correct_cvm:
  forall rs p e ts ts' t annt r ev atp i i' bits bits' e' cvm_tr p',
    filter_remote_disclosures rs p e ts = ts' ->
    In t ts' -> 
    term_to_coreP t atp ->
    annoP_indexed annt t i i' ->
    build_cvmP atp
                     (mk_st (evc bits e) [] p i)
                     (Some tt)
                     (mk_st (evc bits' e') cvm_tr p' i') ->
    
    In ev cvm_tr ->
    In r rs ->
    ~ (discloses_to_remote ev r).
Proof.
*)
    
  



(*
Definition events_discloses_aspid_to_remote (t:Term) (p:Plc) (e:Evidence) (i:ASP_ID) (r:Plc) : Prop :=
  forall reqp reqi annt ev,
  annoP annt t ->
  events annt p e ev ->
  ev = (req reqi reqp r t e) ->
  (discloses_to_remote ev r).
*)





Fixpoint orb_list (l:list bool) : bool :=
  match l with
  | nil => false
  | b::l => orb b (orb_list l)
  end.

Definition orb_list_alt (l:list bool) : bool := existsb (fun b => b) l.

Lemma orb_list_alt_eq : forall (l:list bool),
    orb_list l = orb_list_alt l.
Proof.
  intros.
  induction l; trivial.
Qed.

Definition term_discloses_to_remote_list (t:Term) (p:Plc) (e:Evidence) (l: list (Plc*Evidence)) : bool :=
  let bool_list := map (term_discloses_to_remote t p e) l in
  orb_list bool_list.

Lemma term_remote_disclosures_correct_events: forall t p e r annt ev,
    term_discloses_to_remote t p e r = false -> 
    annoP annt t ->
    events annt p e ev ->
    ~ (discloses_to_remote ev r).
Proof.
  intros.
  unfold not in *; intros.
  generalizeEverythingElse t.
  induction t; ff; intros.
  -
    invc H0.
    destruct_conjs.
    destruct a; ff.
    +
    invc H1.
    invc H2.
    +
    invc H1.
    invc H2.
    +
      
    invc H1.
    invc H2.
    +
      
    invc H1.
    invc H2.
    +
      
    invc H2.
    invc H1.
    +
      invc H1.
      invc H2.
      
  - (* @ case *)
    invc H0.
    destruct_conjs.
    invc H4.
    break_let.
    invc H6; simpl in *.
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.


    (*
    
    assert ( andb (Nat.eqb p p1) (eqb_evidence e e0) = false).
    admit.
    assert (term_discloses_to_remote t p e (p1, e0) = false).
    admit. *)
    invc H1.
    +
    simpl in *.
    invc H2.

    assert (eqb_plc p1 p1 = true).
    {
      apply eqb_plc_refl.
    }
    assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_evidence_refl.
    }
    repeat find_rewrite.
    simpl in *.
    solve_by_inversion.
    
    

    (*
    
    solve_by_inversion.
    
    rewrite PeanoNat.Nat.eqb_refl in H.
    assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. }
    rewrite H1 in *.
    invc H. *)
    +
      eapply IHt.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    +
      simpl in *.
      solve_by_inversion.
  -

    rewrite Bool.orb_false_iff in H.
    destruct_conjs.

    (*
    
    assert (term_discloses_to_remote t1 p e r = false).
    admit.
    assert (term_discloses_to_remote t2 p (eval t1 p e) r = false).
    admit. *)
    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    find_inversion.

    invc H1.
    + (* t1 case *)
      eapply IHt1.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    + (* t2 case *)
      eapply IHt2.
      eassumption.
      econstructor. repeat eexists. eassumption.
      
      assert (eval t1 p e = aeval a p e).
      {
        erewrite eval_aeval.
        rewrite Heqp1.
        simpl. tauto.
      }
      rewrite H1.
      eassumption.
      eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
Qed.


Definition term_discloses_to_remotes (rs: list (Plc*Evidence)) (t:Term) (p:Plc) (e:Evidence) : bool :=
  existsb (term_discloses_to_remote t p e) rs.

Definition filter_remote_disclosures (rs: list (Plc*Evidence)) (p:Plc) (e:Evidence) (ts:list Term):
  list Term := filter (fun t => negb (term_discloses_to_remotes rs t p e)) ts.

Lemma hii{A:Type} : forall (f:A->bool) ls,
    existsb f ls = false ->
    forallb (fun r => negb (f r)) ls = true.
Proof.
  intros.
  generalizeEverythingElse ls.
  induction ls; intros.
  -
    ff.
  -
    ff.
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    
    assert (negb (f a) = true).
    {
      rewrite H. tauto.
    }
    assert (forallb (fun r : A => negb (f r)) ls = true).
    eapply IHls. eassumption.
    rewrite H1. rewrite H2. tauto.
Qed.

Lemma filter_remote_disclosures_correct_events: forall rs p e ts ts' t annt r ev,
  filter_remote_disclosures rs p e ts = ts' ->
  (*In t ts -> *)
  annoP annt t ->
  events annt p e ev ->
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_remote ev r).
(*  ~ (In t ts'). *)
Proof.

  (*
  Check term_remote_disclosures_correct_events.
   *)
  (*
     : forall (t : Term) (p : Plc) (e : Evidence) (r : Plc * Evidence) (annt : AnnoTerm) (ev : Ev),
       term_discloses_to_remote t p e r = false ->
       annoP annt t -> events annt p e ev -> ~ discloses_to_remote ev r
   *)

  (*
  Check filter_In.
   *)
  
  (*
     : forall (A : Type) (f : A -> bool) (x : A) (l : list A), In x (filter f l) <-> In x l /\ f x = true
   *)
  intros.
  unfold filter_remote_disclosures in *.

  eapply term_remote_disclosures_correct_events.
  3: { eassumption. }
  2: { eassumption. }

  rewrite <- H in H3. clear H.
  rewrite filter_In in H3.
  destruct_conjs. clear H.
  unfold term_discloses_to_remotes in *.

  (*
  Check existsb_exists.
   *)
  
  (*
     : forall (A : Type) (f : A -> bool) (l : list A),
       existsb f l = true <-> (exists x : A, In x l /\ f x = true)
   *)

  
  assert ((existsb (term_discloses_to_remote t p e) rs) = false).
  {
    rewrite <- Bool.negb_true_iff.
    eassumption.
  }
  clear H3.

  assert (forall x, In x rs -> term_discloses_to_remote t p e x = false).
  {
    intros.
    assert (forallb (fun r => negb (term_discloses_to_remote t p e r)) rs = true).
    {
      eapply hii.
      eassumption.
    }
    rewrite forallb_forall in H4.
    rewrite <- Bool.negb_true_iff.
    eapply H4.
    eassumption.
  }

  eapply H3. eassumption.
Qed.

Lemma lts_refines_events: forall t p e tr ev,
  well_formed_r_annt t ->
  lstar (conf t p e) tr (stop p (aeval t p e)) ->
  In ev tr ->
  events t p e ev.
Proof.
  intros.
  eapply trace_events; eauto.
  eapply lstar_trace; eauto.
Qed.

(*
Lemma events_refines_lts: forall t p e tr ev,
    events t p e ev ->
    In ev tr ->
    lstar (conf t p e) tr (stop p (aeval t p e)).
Proof.
Admitted.
*)

Lemma filter_remote_disclosures_correct_cvm:
  forall rs p e ts ts' t annt r ev atp i i' bits bits' e' cvm_tr p' ac ac',
    filter_remote_disclosures rs p e ts = ts' ->
    In t ts' -> 
    term_to_coreP t atp ->
    annoP_indexed annt t i i' ->
    build_cvmP atp
                     (mk_st (evc bits e) [] p i ac)
                     (resultC tt)
                     (mk_st (evc bits' e') cvm_tr p' i' ac') ->
    
    In ev cvm_tr ->
    In r rs ->
    ~ (discloses_to_remote ev r).
Proof.
  intros.
  assert (events annt p e ev).
  {
    eapply lts_refines_events.
    -
      invc H2.
      eapply anno_well_formed_r.
      eassumption.
    -
      eapply cvm_refines_lts_events.
      +
        eassumption.
      +
        eassumption.
      +
        eassumption.
        
    -
      eassumption. 
  }
  
  eapply filter_remote_disclosures_correct_events; eauto.
  invc H2.
  econstructor.
  repeat eexists. eassumption.
Qed.





(*
Commenting out ASP disclosure defs and proofs for now....




(* Start ASP disclosures definitions and facts *)


Definition get_aspid (ps:ASP_PARAMS): ASP_ID :=
  match ps with
  | asp_paramsC i _ _ _ => i
  end.

Fixpoint term_discloses_to_asp (t:Term) (p:Plc) (e:Evidence) (r:(Plc*ASP_ID*Evidence)) : bool :=
  match t with
  | asp (ASPC sp _ (asp_paramsC x _ _ _)) =>
    let '(rp,ri,re) := r in
    match sp with
    | NONE => (eqb_evidence re mt)
    | ALL => 
      (Nat.eqb p rp) && (eqb_aspid x ri) && (evsubt_bool re e)  (* (eqb_evidence e re) *)
    end
  | asp SIG =>
    let '(rp,ri,re) := r in
    (Nat.eqb p rp) && (eqb_aspid (get_aspid sig_params) ri) && (evsubt_bool re e) (* (eqb_evidence e re) *)
  | asp HSH =>
    let '(rp,ri,re) := r in
    (Nat.eqb p rp) && (eqb_aspid (get_aspid hsh_params) ri) && (evsubt_bool re e) (* (eqb_evidence e re) *)
  | att q t' => (* (Nat.eqb q (fst r)) && (eqb_evidence e (snd r)) || *)
               (term_discloses_to_asp t' q e r)
  | lseq t1 t2 => (term_discloses_to_asp t1 p e r) ||
                 (term_discloses_to_asp t2 p (eval t1 p e) r)
  | bseq (sp1,sp2) t1 t2 => (term_discloses_to_asp t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_asp t2 p (splitEv_mt sp2 e) r)
  | bpar (sp1,sp2) t1 t2 => (term_discloses_to_asp t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_asp t2 p (splitEv_mt sp2 e) r)
  | _ => false
  end.


Lemma term_asp_disclosures_correct_events: forall t p e r annt ev,
    term_discloses_to_asp t p e r = false -> 
    annoP annt t ->
    events annt p e ev ->
    ~ (discloses_to_asp ev r).
Proof.
  intros.
  unfold not in *; intros.
  generalizeEverythingElse t.
  induction t; ff; intros.
  -
    invc H0.
    destruct_conjs.
    destruct a; ff.
    
    invc H1.
    invc H2.
    invc H1.
    invc H2.

    invc H1.
    invc H2.

    rewrite PeanoNat.Nat.eqb_refl in H.

    assert (eqb_aspid a0 a0 = true).
    {
      apply eqb_eq_aspid. auto.
    }
    rewrite H0 in *; clear H0.
    invc H.
    

    (*
     assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. }
     *)

    rewrite evsubt_bool_prop_iff in H1.
    rewrite H1 in *.
    solve_by_inversion.

    (*
    
    rewrite H0 in *; clear H0.
    assert (eqb_aspid a0 a0 = true).
    {
      apply eqb_eq_aspid. auto.
    }
    rewrite H0 in *; clear H0.
    invc H. *)

    

    invc H1.
    simpl in *.
    invc H2.

    assert (eqb_evidence mt mt = true).
    {
      apply eqb_eq_evidence. auto. }
    invc H1.
    rewrite H0 in *.
    solve_by_inversion.

    invc H1.
    invc H2.

    destruct sig_params.
    ff.

    rewrite PeanoNat.Nat.eqb_refl in H.

    (*
     assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. } *)
    assert (eqb_aspid a a = true).
    {
      apply eqb_eq_aspid. auto.
    }
    rewrite H0 in *; clear H0.
    invc H.
    rewrite evsubt_bool_prop_iff in H1.
    rewrite H1 in *. solve_by_inversion.

    (*

    
    assert (evsubt_bool e0 e = false).
    {
      admit.
    }
    
    rewrite H0 in *; clear H0.
    assert (eqb_aspid a a = true).
    {
      apply eqb_eq_aspid. auto.
    }
    rewrite H0 in *; clear H0.
    invc H. *)

     invc H1.
    invc H2.

    destruct hsh_params.
    ff.

    rewrite PeanoNat.Nat.eqb_refl in H.

    assert (eqb_aspid a a = true).
    {
      apply eqb_eq_aspid. auto.
    }
    rewrite H0 in *; clear H0.
    invc H.
    rewrite evsubt_bool_prop_iff in H1.
    rewrite H1 in *. solve_by_inversion.

(*
    
     assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. }
    rewrite H0 in *; clear H0.
    assert (eqb_aspid a a = true).
    {
      apply eqb_eq_aspid. auto.
    }
    rewrite H0 in *; clear H0.
    invc H.
*)

    
    
      

  -
    invc H0.
    destruct_conjs.
    invc H4.
    break_let.
    invc H6; simpl in *.
    (*
    rewrite Bool.orb_false_iff in H.
    destruct_conjs. *)


    (*
    
    assert ( andb (Nat.eqb p p1) (eqb_evidence e e0) = false).
    admit.
    assert (term_discloses_to_remote t p e (p1, e0) = false).
    admit. *)
    invc H1.
    +
    simpl in *.
    invc H2.

    (*
    rewrite PeanoNat.Nat.eqb_refl in H.
    assert (eqb_evidence e0 e0 = true).
    {
      apply eqb_eq_evidence. auto. }
    rewrite H1 in *.
    invc H. *)
    +
      eapply IHt.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    +
      simpl in *.
      solve_by_inversion.
  -

    rewrite Bool.orb_false_iff in H.
    destruct_conjs.

    (*
    
    assert (term_discloses_to_remote t1 p e r = false).
    admit.
    assert (term_discloses_to_remote t2 p (eval t1 p e) r = false).
    admit. *)
    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    find_inversion.

    invc H1.
    + (* t1 case *)
      eapply IHt1.
      eassumption.
      econstructor. repeat eexists. eassumption.
      eassumption.
      eassumption.
    + (* t2 case *)
      eapply IHt2.
      eassumption.
      econstructor. repeat eexists. eassumption.
      
      assert (eval t1 p e = aeval a0 p e).
      {
        erewrite eval_aeval.
        rewrite Heqp1.
        simpl. tauto.
      }
      rewrite H1.
      eassumption.
      eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
  -
    rewrite Bool.orb_false_iff in H.
    destruct_conjs.
    (*
    assert (term_discloses_to_remote t1 p (splitEv_mt s0 e) r = false).
    admit.
    assert (term_discloses_to_remote t2 p (splitEv_mt s1 e) r = false).
    admit.
     *)
    

    invc H0.
    destruct_conjs.
    invc H5.
    repeat break_let.
    ff.
    invc H1; ff.
    + (* t1 case *)
      destruct s0.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt1.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
    + (* t2 case *)
      destruct s0.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
      ++
        eapply IHt2.
        eassumption.
        econstructor. repeat eexists. eassumption.
        simpl. eassumption.
        eassumption.
Qed.





(*
Definition term_discloses_to_remotes (rs: list (Plc*Evidence)) (t:Term) (p:Plc) (e:Evidence) : bool :=
  existsb (term_discloses_to_remote t p e) rs.

Definition filter_remote_disclosures (rs: list (Plc*Evidence)) (p:Plc) (e:Evidence) (ts:list Term):
  list Term := filter (fun t => negb (term_discloses_to_remotes rs t p e)) ts.
*)


Definition term_discloses_to_asps (ls: list (Plc*ASP_ID*Evidence)) (t:Term) (p:Plc) (e:Evidence) : bool :=
  existsb (term_discloses_to_asp t p e) ls.

Definition filter_asp_disclosures (ls: list (Plc*ASP_ID*Evidence)) (p:Plc) (e:Evidence) (ts:list Term):
  list Term := filter (fun t => negb (term_discloses_to_asps ls t p e)) ts.



Lemma filter_asp_disclosures_correct_events: forall rs p e ts ts' t annt r ev,
  filter_asp_disclosures rs p e ts = ts' ->
  In t ts ->
  annoP annt t ->
  events annt p e ev ->
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_asp ev r).
(*  ~ (In t ts'). *)
Proof.
  intros.
  unfold filter_asp_disclosures in *.

  eapply term_asp_disclosures_correct_events.
  3: { eassumption. }
  2: { eassumption. }

  rewrite <- H in H4. clear H.
  rewrite filter_In in H4.
  destruct_conjs. clear H.
  unfold term_discloses_to_asps in *.
  Check existsb_exists.
  (*
     : forall (A : Type) (f : A -> bool) (l : list A),
       existsb f l = true <-> (exists x : A, In x l /\ f x = true)
   *)

  
  assert ((existsb (term_discloses_to_asp t p e) rs) = false).
  {
    rewrite <- Bool.negb_true_iff.
    eassumption.
  }
  clear H4.

  assert (forall x, In x rs -> term_discloses_to_asp t p e x = false).
  {
    intros.
    assert (forallb (fun r => negb (term_discloses_to_asp t p e r)) rs = true).
    {
      eapply hii.
      eassumption.
    }
    rewrite forallb_forall in H5.
  (*
Bool.negb_false_iff: forall b : bool, negb b = false <-> b = true
Bool.negb_true_iff: forall b : bool, negb b = true <-> b = false
   *)
      rewrite <- Bool.negb_true_iff.
      eapply H5.
      eassumption.
  }

  eapply H4. eassumption.
Qed.




Lemma filter_asp_disclosures_correct_cvm:
  forall rs p e ts ts' t annt r ev atp i i' bits bits' e' cvm_tr p',
  filter_asp_disclosures rs p e ts = ts' ->
  In t ts ->

  term_to_coreP t atp ->
  (*anno_parP atp t -> *)
  annoP_indexed annt t i i' ->
  copland_compileP atp
                   (mk_st (evc bits e) [] p i)
                   (Some tt)
                   (mk_st (evc bits' e') cvm_tr p' i') ->

  In ev cvm_tr ->
  
  In r rs ->
  In t ts' -> 
  ~ (discloses_to_asp ev r).
 (*  ~ (In t ts'). *)
Proof.
  intros.
  assert (events annt p e ev).
  {
    eapply lts_refines_events.
    -
      invc H2.
      eapply anno_well_formed_r.
      eassumption.
    -
      eapply cvm_refines_lts_events.
      +
        eassumption.
      +
        eassumption.
      +
        eassumption.
        
    -
      eassumption. 
  }
  
  eapply filter_asp_disclosures_correct_events; eauto.
  invc H2.
  econstructor.
  repeat eexists. eassumption.
Qed.





(* 
END OF:  Commenting out ASP disclosure defs and proofs for now....
*)  *)





  



(*

(* Helper relation for "discloses" relation *)
Inductive asp_discloses: ASP -> Plc -> Evidence -> (Plc * Evidence) -> Prop :=
| cpy_dis: forall p e,
    asp_discloses CPY p e (p,e)
| asp_dis: forall p e args,
    asp_discloses (ASPC args) p e (p, (uu args p e))
| sig_dis: forall p e,
    asp_discloses SIG p e (p, (gg p e))
| hsh_dis: forall p e,
    asp_discloses HSH p e (p, (hh p e)).


(* Relation that specifies evidence disclosure.  Technically, it specifies the 
   TYPE of evidence disclosed to each place. 

   Parameters--  discloses t p e (q,e') says: executing phrase t at place p 
   with initial evidence type e discloses evidence type e' to place q.

   For example:

   discloses (att q t) p e (q,e) states that evidence of type e is disclosed
   to place q.  

*)
Inductive discloses: Term -> Plc -> Evidence -> (Plc * Evidence) -> Prop :=
| asp_discl: forall a p e v,
    asp_discloses a p e v ->
    discloses (asp a) p e v
| att_discl: forall t p q e v,
    discloses t q e v ->
    discloses (att q t) p e v
| lseq_discl_l: forall t1 t2 p e v,
    discloses t1 p e v ->
    discloses (lseq t1 t2) p e v
| lseq_discl_r: forall t1 t2 p e v,
    discloses t2 p (eval t1 p e) v ->
    discloses (lseq t1 t2) p e v
| bseq_discl_l: forall t1 t2 p e v sp2,
    discloses t1 p e v ->
    discloses (bseq (ALL, sp2) t1 t2) p e v
| bseq_discl_r: forall t1 t2 p e v sp1,
    discloses t2 p e v ->
    discloses (bseq (sp1, ALL) t1 t2) p e v
| bpar_discl_l: forall t1 t2 p e v sp2,
    discloses t1 p e v ->
    discloses (bpar (ALL, sp2) t1 t2) p e v
| bpar_discl_r: forall t1 t2 p e v sp1,
    discloses t2 p e v ->
    discloses (bpar (sp1, ALL) t1 t2) p e v.

*)
              
  
                                               
