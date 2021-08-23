Require Import ConcreteEvidence Appraisal_Defs StVM Impl_vm Impl_appraisal Auto AutoApp External_Facts MonadVM Helpers_VmSemantics VmSemantics.

Require Import Coq.Program.Tactics Lia.

Require Import List.
Import ListNotations.


Ltac evsub_ih :=
  match goal with
  | [H: EvSub _ ?e,
        IH: context[EvSub _ ?e -> _] |- _] =>
    edestruct IH; [eauto | eauto ]
  end.

Lemma uuc_app: forall e' e'' i args tpl tid n,
    EvSub (uuc i args tpl tid n e'') e' ->
    exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                 (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff;
    try evSubFacts; eauto;
      try evsub_ih.
Defined.

Lemma hhc_app: forall e' p bs et,
    EvSub (hhc p bs et) e' ->
    EvSub (hhc p (checkHash et p bs) et)
          (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff;
    try evSubFacts;
    eauto.
Defined.

Lemma etfun_reconstruct: forall e e0 e1,
    Some e = reconstruct_ev' e0 e1 ->
    e1 = et_fun e.
Proof.
  intros.
  generalizeEverythingElse e1.
  induction e1; intros;
    repeat ff;
    repeat jkjke.
Defined.

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
    end.

Ltac find_wfec :=
  repeat 
    match goal with
    | [H: context [well_formed_r ?t -> _](*
                   wf_ec _ ->
                   copland_compile _ _ _ = _ ->
                   wf_ec _]*),
          H2: well_formed_r ?t,
              H3: wf_ec ?e,
                  H4: copland_compile ?t
                                      {| st_ev := ?e; st_trace := _; st_pl := _ |} =
                      (_, {| st_ev := ?e'; st_trace := _; st_pl := _ |})
       |- _ ] => 
      assert_new_proof_by
        (wf_ec e')
        
        ltac:(eapply H; [apply H2 | apply H3 | apply H4])
    end.

Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
    end.

Lemma wfec_split: forall e s,
    wf_ec e ->
    wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e).
Proof.
  intros.
  split;
    destruct s; ff; try unfold mt_evc; ff;
      econstructor; ff.
Defined.

Ltac do_wfec_split :=
  match goal with
  | [H: context[splitEv_l ?s ?e],
        H2: context[splitEv_r ?s ?e],
            H3: wf_ec ?e
     |- _] =>
    
    assert_new_proof_by
      (wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e))
      ltac: (eapply wfec_split; apply H3)
  end; destruct_conjs.

Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p',
    well_formed_r t1 ->
    wf_ec e ->
    copland_compile t1
                    {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt,
     {| st_ev := e'; st_trace := tr'; st_pl := p' |}) ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  -
    destruct a; ff;
      invc H0;
      try (
          econstructor;
          ff;
          try tauto;
          try congruence).  
  -
    ff.
    do_wf_pieces.

    eapply IHt1;
      try eassumption.

    apply copland_compile_at;
      try eassumption.
  -
    repeat ff.
    vmsts.
    do_wf_pieces.
  -
    repeat ff; vmsts; subst.
    do_wf_pieces.

    do_wfec_split.

    find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.

  -
    repeat ff; vmsts; subst.
    do_wf_pieces.

    do_wfec_split.

    find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.   
Defined.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [H: well_formed_r ?t,
          H2: wf_ec ?stev,
              H3: copland_compile ?t
                                  {| st_ev := ?stev; st_trace := _; st_pl := _ |} =
                  (Some tt,
                   {| st_ev := ?stev'; st_trace := _; st_pl := _ |})
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [apply H | apply H2 | apply H3])
                                 
    end.

Lemma some_recons' : forall e x,
    length e = S x ->
    exists bs ls', peel_bs e = Some (bs, ls').
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.

Ltac do_some_recons' :=
  match goal with
  | [H: length ?e = S _ |- _ ] =>
    edestruct some_recons'; [apply H | idtac]
                              
  end; destruct_conjs; jkjke.

Ltac do_rcih :=
  match goal with
  | [H: context[reconstruct_ev' _ _]
               

     |- context[reconstruct_ev' ?e' ?et] ] =>
    assert_new_proof_by
      (exists x, Some x = reconstruct_ev' e' et)
      ltac:(eapply H with (e:=e');
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.

Lemma some_recons : forall e,
    wf_ec e ->
    exists ee, Some ee = reconstruct_ev e.
Proof.
  intros.
  destruct e.
  generalizeEverythingElse e0.
  induction e0; intros;
    try (ff; eauto; tauto);
    try
      ( inv_wfec; ff;
        do_some_recons');
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke');
    try ( inv_wfec; ff;
          repeat do_rcih;
          destruct_conjs;
          repeat jkjke').
  assert (e = []).
  { destruct e; try solve_by_inversion. }
  ff.
  eauto.
  destruct e; try solve_by_inversion.
  ff.
  destruct e; try solve_by_inversion.
  ff.
Defined.

Ltac do_somerecons :=
  repeat
    match goal with
    | [H: wf_ec ?e
       |- _ ] =>
      assert_new_proof_by
        (exists x, Some x = reconstruct_ev e)
        ltac:(eapply some_recons; apply H)     
    end; destruct_conjs.

Ltac do_evsub_ih :=
  match goal with
  | [H: copland_compile ?t1 {| st_ev := _; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
        H2: copland_compile ?t2 {| st_ev := ?stev'; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?v = reconstruct_ev ?stev

     |- context[EvSub ?e'' _ \/ _]] =>
    
    assert_new_proof_by
      (EvSub e'' v \/
       (exists (ett : Evidence) (p'0 bs : nat),
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
      eauto
  end.

Ltac do_evsubh_ih :=
  match goal with
  | [H: EvSub (hhc ?H2 ?H3 ?H4) _

     |- context[EvSub _ ?e' \/ _]] =>
    
    assert_new_proof_by
      (EvSub (hhc H2 H3 H4) e' \/
       (exists (ett : Evidence) (p'0 bs : nat),
           EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun (hhc H2 H3 H4)) ett))
      eauto
  end.

Ltac do_hh_sub :=
  match goal with
  | [H: context[(hh ?H2 ?H3)]

     |- context[EvSubT ?e'' _]] =>
    
    assert_new_proof_by
      (EvSubT e'' (hh H2 H3))
      ltac: (eapply evsubT_transitive; eauto)
  end.

Lemma wfec_firstn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    firstn (et_size e1) (e0 ++ e2) = e0.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply More_lists.firstn_append.
Defined.

Ltac do_wfec_firstn :=
  match goal with
  | [H: context[(firstn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (firstn (et_size e1) (e0 ++ e2) = e0)
      ltac: (eapply wfec_firstn; apply H2)
  end.

Lemma wfec_skipn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    skipn (et_size e1) (e0 ++ e2) = e2.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply More_lists.skipn_append.
Defined.

Ltac do_wfec_skipn :=
  match goal with
  | [H: context[(skipn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (skipn (et_size e1) (e0 ++ e2) = e2)
      ltac: (eapply wfec_skipn; apply H2)
  end.

Lemma fold_recev: forall e0 e1,
    reconstruct_ev' e0 e1 = reconstruct_ev (evc e0 e1).
Proof.
  ff.
  tauto.
Defined.

Ltac clear_skipn_firstn :=
  match goal with
  | [H: firstn _ _ = _,
        H2: skipn _ _ = _ |- _]
    => rewrite H in *; clear H;
      rewrite H2 in *; clear H2
  end.

Lemma not_none_alseq_pieces: forall r t1 t2,
    not_none_none (alseq r t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply alseq_subr.
    eassumption.
Defined.

Lemma not_none_abseq_pieces: forall r s t1 t2,
    not_none_none (abseq r s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abseq_subr.
    eassumption.
Defined.

Lemma not_none_abpar_pieces: forall r s t1 t2,
    not_none_none (abpar r s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abpar_subr.
    eassumption.
Defined.

Lemma not_none_aatt_pieces: forall r q t1,
    not_none_none (aatt r q t1) ->
    not_none_none t1.
Proof.
  intros.
  unfold not_none_none in *.
  intros.
  unfold not. intros.
  specialize H with (t':=t').
  concludes.
  unfold not in *.
  apply H.
  econstructor.
  eassumption.
Defined.

Lemma not_hshsig_alseq_pieces: forall r t1 t2,
    not_hash_sig_term (alseq r t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  unfold not_hash_sig_term in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply alseq_subr.
    eassumption.
Defined.

Lemma not_hshsig_abseq_pieces: forall r s t1 t2,
    not_hash_sig_term (abseq r s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  unfold not_hash_sig_term in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abseq_subr.
    eassumption.
Defined.

Lemma not_hshsig_abpar_pieces: forall r s t1 t2,
    not_hash_sig_term (abpar r s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  unfold not_hash_sig_term in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abpar_subr.
    eassumption.
Defined.

Lemma not_hshsig_aatt_pieces: forall r q t1,
    not_hash_sig_term (aatt r q t1) ->
    not_hash_sig_term t1.
Proof.
  intros.
  unfold not_hash_sig_term in *.
  intros.
  unfold not. intros.
  specialize H with (t':=t').
  concludes.
  unfold not in *.
  apply H.
  econstructor.
  eassumption.
Defined.


Ltac do_not_none_alseq_pieces :=
  match goal with
  | [H: not_none_none (alseq _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_alseq_pieces; apply H)
  end.

Ltac do_not_none_abseq_pieces :=
  match goal with
  | [H: not_none_none (abseq _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abseq_pieces; apply H)
  end.

Ltac do_not_none_abpar_pieces :=
  match goal with
  | [H: not_none_none (abpar _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abpar_pieces; apply H)
  end.

Ltac do_not_none_aatt_pieces :=
  match goal with
  | [H: not_none_none (aatt _ _ ?t1)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1)
      ltac:(eapply not_none_aatt_pieces; apply H)
  end.

Ltac do_not_none :=
  try do_not_none_aatt_pieces;
  try do_not_none_alseq_pieces;
  try do_not_none_abseq_pieces;
  try do_not_none_abpar_pieces;
  destruct_conjs.


Ltac do_not_hshsig_alseq_pieces :=
  match goal with
  | [H: not_hash_sig_term (alseq _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_alseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abseq_pieces :=
  match goal with
  | [H: not_hash_sig_term (abseq _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abpar_pieces :=
  match goal with
  | [H: not_hash_sig_term (abpar _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abpar_pieces; apply H)
  end.

Ltac do_not_hshsig_aatt_pieces :=
  match goal with
  | [H: not_hash_sig_term (aatt _ _ ?t1)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1)
      ltac:(eapply not_hshsig_aatt_pieces; apply H)
  end.

Ltac do_not_hshsig :=
  try do_not_hshsig_aatt_pieces;
  try do_not_hshsig_alseq_pieces;
  try do_not_hshsig_abseq_pieces;
  try do_not_hshsig_abpar_pieces;
  destruct_conjs.


Lemma evsubt_preserved_aeval: forall t et ett p,
    not_none_none t ->
    EvSubT ett et ->
    EvSubT ett (aeval t p et).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff.
  -
    destruct a; ff.
    apply uuSubT.
    eauto.
  -
    do_not_none.
    eauto.
  -
    do_not_none.
    eauto.
  -
    do_not_none.
    destruct s.
    destruct s; destruct s0; ff.
    
    unfold not_none_none in H.
    unfold not in *.
    exfalso.
    eapply H with (t' := (abseq r (NONE, NONE) t1 t2)).
    econstructor.
    repeat eexists.
    econstructor.
  -
    do_not_none.
    destruct s.
    destruct s; destruct s0; ff.
    
    unfold not_none_none in H.
    unfold not in *.
    exfalso.
    eapply H with (t' := (abpar r (NONE, NONE) t1 t2)).
    right.
    repeat eexists.
    econstructor.
Defined.

Lemma evsubt_preserved: forall t e e' et et' tr tr' p p' ett,
    well_formed_r t ->
    not_none_none t ->
    copland_compile t {| st_ev := evc e et; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e' et'; st_trace := tr'; st_pl := p' |}) ->
    EvSubT ett et ->
    EvSubT ett et'.
Proof.
  intros.
  assert (et' = Term_Defs.eval (unanno t) p et).
  {
    eapply cvm_refines_lts_evidence; eauto.
  }
  subst.

  rewrite eval_aeval.
  eapply evsubt_preserved_aeval; eauto.
Defined.

Lemma not_ev: forall t e,
    not_hash_sig_term_ev t e ->
    not_hash_sig_ev e.
Proof.
  intros.
  cbv in H.
  destruct_conjs.
  cbv.
  destruct_conjs.
  intros.
  destruct_conjs.
  subst.
  eapply H0.
  repeat eexists.
  eassumption.
  eassumption.
Defined.

Lemma etfun_exists: forall y,
    exists y', y = et_fun y'.
Proof.
  intros.
  induction y; intros.
  -
    exists mtc.
    eauto.
  -
    destruct_conjs.
    exists (uuc n l n0 n1 1 IHy).
    ff.
  -
    destruct_conjs.
    exists (ggc n 1 IHy).
    ff.
  -
    destruct_conjs.
    exists (hhc n 1 y).
    ff.
  -
    exists (nnc n 1).
    ff.
  -
    destruct_conjs.
    exists (ssc IHy1 IHy2).
    ff.
  -
    destruct_conjs.
    exists (ppc IHy1 IHy2).
    ff.
Defined.

Lemma not_hshsig_uuc: forall e' n l n1 n2 x,
    not_hash_sig_ev e' ->
    not_hash_sig_ev (uuc n l n1 n2 x e').
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  intros.
  unfold not in *; intros.
  invc H1.
  unfold hash_sig_ev in H0.
  destruct_conjs.
  invc H5.
  eapply H.
  eassumption.
  eassumption.
Defined.

Lemma not_hshsig_ggc: forall e' n bs,
    not_hash_sig_ev e' ->
    not_hash_sig_ev (ggc n bs e').
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  intros.
  unfold not in *; intros.
  invc H1.
  unfold hash_sig_ev in H0.
  destruct_conjs.
  invc H5.
  eapply H.
  eassumption.
  eassumption.
Defined.

Lemma gg_recons: forall e ecc x y,
    Some e = reconstruct_ev ecc ->
    EvSubT (gg x y) (get_et ecc) ->
    gg_sub e.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros; ff.
  -
    destruct ecc; ff.
    assert (e0 = mt).
    {
      destruct e0; repeat ff; try solve_by_inversion.
    }
    subst.
    invc H0.
  -
    destruct ecc; ff.
    assert (e0 = nn n).
    {
      destruct e0; repeat ff; try solve_by_inversion.
    }
    subst.
    invc H0.
  -
    destruct ecc; ff.
    assert (exists et', e1 = uu n l n0 n1 et').
    {
      destruct e1; repeat ff; try solve_by_inversion.
      eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H0.
    rewrite fold_recev in *.
    assert (gg_sub e2).
    {
      
      eapply IHe with (ecc:=(evc e1 H1)).
      symmetry.
      apply Heqo0.
      ff.
      eassumption.
    }
    invc H.
    destruct_conjs.
    subst.
    econstructor.
    repeat eexists.
    apply uuSub.
    eassumption.
  -
    destruct ecc; ff.
    econstructor.
    repeat eexists.
    eauto.
  -
    destruct ecc; ff.
    assert (e1 = hh n e).
    {
      eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
    invc H0.
    assert (exists y', y = et_fun y').
    {
      eapply etfun_exists.
    }
    destruct_conjs.
    subst.
    
    econstructor.
    repeat eexists.
    eapply hhSub.
    ff.
    eassumption.
  -
    destruct ecc; ff.
    assert (exists et1 et2, e0 = ss et1 et2).
    {
      eapply inv_recon_ss; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H0.
    +
      assert (gg_sub e0).
      {
        rewrite fold_recev in *.
        eapply IHe1.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      invc H.
      destruct_conjs.
      subst.
      econstructor.
      repeat eexists.
      apply ssSubl.
      eassumption.
    +
      assert (gg_sub e3).
      {
        rewrite fold_recev in *.
        eapply IHe2.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      invc H.
      destruct_conjs.
      subst.
      econstructor.
      repeat eexists.
      apply ssSubr.
      eassumption.
  -
    destruct ecc; ff.
    assert (exists et1 et2, e0 = pp et1 et2).
    {
      eapply inv_recon_pp; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H0.
    +
      assert (gg_sub e0).
      {
        rewrite fold_recev in *.
        eapply IHe1.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      invc H.
      destruct_conjs.
      subst.
      econstructor.
      repeat eexists.
      apply ppSubl.
      eassumption.
    +
      assert (gg_sub e3).
      {
        rewrite fold_recev in *.
        eapply IHe2.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      invc H.
      destruct_conjs.
      subst.
      econstructor.
      repeat eexists.
      apply ppSubr.
      eassumption.
      Unshelve.
      eauto.
Defined.

Lemma hh_recons: forall e ecc x y,
    Some e = reconstruct_ev ecc ->
    EvSubT (hh x y) (get_et ecc) ->
    exists bs, EvSub (hhc x bs y) e.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros; ff.
  -
    destruct ecc; ff.
    assert (e0 = mt).
    {
      destruct e0; repeat ff; try solve_by_inversion.
    }
    subst.
    invc H0.
  -
    destruct ecc; ff.
    assert (e0 = nn n).
    {
      destruct e0; repeat ff; try solve_by_inversion.
    }
    subst.
    invc H0.
  -
    destruct ecc; ff.
    assert (exists et', e1 = uu n l n0 n1 et').
    {
      destruct e1; repeat ff; try solve_by_inversion.
      eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H0.
    rewrite fold_recev in *.

    edestruct IHe.
    jkjke'.
    ff.
    eassumption.
    repeat eexists.
    apply uuSub.
    eassumption.
  -
    destruct ecc; ff.
    assert (exists et', e1 = gg n et').
    {
      eapply inv_recon_gg; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    rewrite fold_recev in *.
    invc H0.
    edestruct IHe.
    symmetry.
    eassumption.
    ff.
    eassumption.
    repeat eexists.
    apply ggSub.
    eassumption.

  -
    destruct ecc; ff.
    assert (e1 = hh n e).
    {
      eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
    invc H0.
    eauto.
    eauto.

  -
    destruct ecc; ff.
    assert (exists et1 et2, e0 = ss et1 et2).
    {
      eapply inv_recon_ss; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H0.
    +
      rewrite fold_recev in *.
      edestruct IHe1.
      symmetry.
      eassumption.
      ff.
      eassumption.

      repeat eexists.
      apply ssSubl. eassumption.
    +
      (*
      assert (gg_sub e0).
      {
       *)
      rewrite fold_recev in *.
      edestruct IHe2.
      symmetry.
      eassumption.
      ff.
      eassumption.

      repeat eexists.
      apply ssSubr. eassumption.
  -
    destruct ecc; ff.
    assert (exists et1 et2, e0 = pp et1 et2).
    {
      eapply inv_recon_pp; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H0.
    +
      rewrite fold_recev in *.
      edestruct IHe1.
      symmetry.
      eassumption.
      ff.
      eassumption.

      repeat eexists.
      apply ppSubl. eassumption.
    +
      rewrite fold_recev in *.
      edestruct IHe2.
      symmetry.
      eassumption.
      ff.
      eassumption.

      repeat eexists.
      apply ppSubr. eassumption.
      Unshelve.
      eauto.
Defined.

Lemma evAccum: forall t p (e e' e'':EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
    not_none_none t ->
    wf_ec ecc ->
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->
    EvSub e'' e ->
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (
      (EvSub e'' e') \/
      (exists ett p' bs,
          EvSub (hhc p' bs ett) e' /\
          EvSubT (et_fun e'') ett
      )
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      repeat ff;
      try jkjke';
      try unfold cons_uu in *;
      try unfold cons_gg in *;
      (repeat ff; try eauto).
    +
      destruct ecc.
      ff.
      assert (e2 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.
      jkjke'.
      ff.
    +
      destruct ecc.
      ff.
      assert (e1 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.
      right.
      repeat eexists.
      econstructor.
      apply evsub_etfun; eauto.
      
  - (* aatt case *)
    do_wf_pieces.
    do_not_none.
    ff.
    
    eapply IHt.
    eassumption.

    2: {
      apply H1.
    }
    2: {
      eassumption. }
    2: {
      
      eassumption. }
    2: {
      eassumption. }
    2: {
      apply copland_compile_at.
      eassumption.
    }
    eassumption.

  - (* alseq case *)
    ff.
    dosome.
    vmsts.

    do_wf_pieces.

    do_wfec_preserved.

    do_somerecons.

    do_not_none.

    do_evsub_ih.
    
    door.
    +
      eapply IHt2 with (ecc:=st_ev); eauto.
    +

      do_evsubh_ih.
      
      door.
      ++
        right.
        repeat (eexists; eauto).
      ++
        destruct_conjs.
        ff.
        
        right.
        repeat (eexists; eauto).
        do_hh_sub.
        eapply evsubT_transitive; eauto.
        
  - (* abseq case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_wfec_preserved.

    do_somerecons.

    do_not_none.
    
    destruct s; destruct s; destruct s0;

      try (
          ff;
          try unfold mt_evc in *;
          repeat jkjke';
          ff;
          rewrite fold_recev in *;
          do_evsub_ih;
          
          ff;
          
          door; destruct_conjs;
          try eauto;
          try (right; repeat (eexists; eauto))
        ).

    unfold not_none_none in *.
    specialize H0 with (t':= (abseq (n,n0) (NONE, NONE) t1 t2)).
    assert (~
              term_sub (abseq (n, n0) (NONE, NONE) t1 t2)
              (abseq (n, n0) (NONE, NONE) t1 t2)).
    {
      apply H0.
      unfold none_none_term.
      left.
      eauto.
    }
    unfold not in H22.
    exfalso.
    apply H22.
    econstructor.

  - (* abpar case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_wfec_preserved.

    do_somerecons.

    do_not_none.
    
    destruct s; destruct s; destruct s0;

      try (
          ff;
          try unfold mt_evc in *;
          repeat jkjke';
          ff;
          rewrite fold_recev in *;
          do_evsub_ih;
          
          ff;
          
          door; destruct_conjs;
          try eauto;
          try (right; repeat (eexists; eauto))
        ).

    unfold not_none_none in *.
    specialize H0 with (t':= (abpar (n,n0) (NONE, NONE) t1 t2)).
    assert (~
              term_sub (abpar (n, n0) (NONE, NONE) t1 t2)
              (abpar (n, n0) (NONE, NONE) t1 t2)).
    apply H0.
    unfold none_none_term.
    eauto.
    (*
    left.
    eauto. *)
    unfold not in H22.
    exfalso.
    apply H22.
    econstructor.
Defined.

Ltac do_evaccum :=
  repeat 
    match goal with
    | [ H: well_formed_r ?t,
           H2: wf_ec ?ecc,
               H3: Some ?e = reconstruct_ev ?ecc,
                   H4: Some ?e' = reconstruct_ev ?ecc',
                       H5: EvSub ?e'' ?e,
                           H6: copland_compile ?t
                                               {| st_ev := ?ecc; st_trace := _; st_pl := _ |} =
                               (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}),
                               H7: not_none_none ?t

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H | apply H7 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
    end.

Lemma sig_term_ev_lseq: forall r t1 t2 e e0 e1 e2 e3 tr tr' p p',
    not_hash_sig_term_ev (alseq r t1 t2) e ->
    copland_compile t1 {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |}) ->
    Some e  = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t1 e.
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  split.
  -

    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eassumption.
    eassumption.
    apply alseq_subl.
    eassumption.
  -  
    split; eauto.
    unfold not.
    intros.
    destruct_conjs.
    eapply H3.

    eassumption.
    invc H5.
    econstructor.
    apply alseq_subl.
    eassumption.
Defined.

Lemma sig_is: forall t ecc ecc' e e' tr tr' p p',

    well_formed_r t ->
    wf_ec ecc ->
    copland_compile t
                    {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt,
     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    Some e = reconstruct_ev ecc ->
    Some e' = reconstruct_ev ecc' ->

    gg_sub e' ->

    gg_sub e \/
    exists r, term_sub (aasp r SIG) t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; repeat ff.
  -
    jkjke'.
    ff.
  -
    unfold cons_uu in *.
    repeat ff.
    invc H4.
    destruct_conjs.
    subst.
    invc H5.
    left.
    econstructor.
    eauto.
  -
    invc H4.
    destruct_conjs.
    subst.
    invc H6.
    +
      right.
      exists (n, n0).
      econstructor.
    +
      destruct ecc; ff.
      jkjke'.
      ff.
      right.
      eexists.
      econstructor.
  -
    invc H4.
    destruct_conjs.
    subst.
    invc H6.
    ff.
    left.
    eapply gg_recons; eauto.
  -
    do_wf_pieces.

    edestruct IHt.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
    apply H2.
    eassumption.
    eassumption.
    left. eauto.
    destruct_conjs.
    right.
    eexists.
    econstructor.
    eassumption.
  -
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.

    assert (gg_sub H9 \/ (exists r, term_sub (aasp r SIG) t2)).
    {
      eapply IHt2.
      eassumption.
      apply H6.
      eassumption.
      eassumption.
      jkjke'.
      jkjke'.
      jkjke'.
      ff.
    }
    door.

    assert (gg_sub e \/ (exists r, term_sub (aasp r SIG) t1)).
    {
      eapply IHt1.
      eassumption.
      2: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      eassumption.
    }

    door.
    eauto.
    right.
    eexists.
    apply alseq_subl. eassumption.

    right.
    eexists.
    apply alseq_subr. eassumption.
  - (* abseq case *)

    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    repeat find_rewrite.
    vmsts.
    invc H4.
    destruct_conjs.
    subst.
    invc H16.
    +
      ff.
      rewrite fold_recev in *.

      clear H11; clear H12.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t1).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.
          
          econstructor.
          eauto.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          jkjke'.
          jkjke'.
          repeat ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          repeat ff.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++
            right.
            eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: {eassumption. }
            
            eassumption.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.       
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++   
            right.
            eauto.
      }
      door.
      ++
        eauto.
      ++
        right.
        eexists.
        apply abseq_subl.
        eassumption.
    +
      ff.
      
      rewrite fold_recev in *.

      clear H11; clear H12.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t2).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++
            right.
            eauto.
        ++
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++
            right.
            eauto.

      }
      door.
      ++
        eauto.
      ++
        right.
        eexists.
        apply abseq_subr.
        eassumption.

  - (* abpar case *)

    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    repeat find_rewrite.
    vmsts.
    invc H4.
    destruct_conjs.
    subst.
    invc H16.
    +
      ff.
      
      rewrite fold_recev in *.

      clear H11; clear H12.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t1).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.
          
          econstructor.
          eauto.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          jkjke'.
          jkjke'.
          repeat ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          repeat ff.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++
            right.
            eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: {eassumption. }
            
            eassumption.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.       
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++   
            right.
            eauto.
      }
      door.
      ++
        eauto.
      ++
        right.
        eexists.
        apply abpar_subl.
        eassumption.
    +
      ff.
      
      rewrite fold_recev in *.

      clear H11; clear H12.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t2).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++
            right.
            eauto.
        ++
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
            eauto.
          }
          door.
          +++
            invc H22.
            destruct_conjs.
            subst.
            solve_by_inversion.
          +++
            right.
            eauto.

      }
      door.
      ++
        eauto.
      ++
        right.
        eexists.
        apply abpar_subr.
        eassumption.
Defined.

Lemma sig_term_ev_bseql: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abseq r s t1 t2) e ->
    copland_compile t1 {| st_ev := splitEv_l s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t1 (splitEvl s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eassumption.
    eassumption.
    apply abseq_subl.
    eassumption.
  -
    destruct s.
    destruct s; destruct s0; ff.
    +
      split; eauto.

      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abseq_subl.
      eassumption.
    +
      split; eauto.

      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abseq_subl.
      eassumption.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
Defined.

Lemma sig_term_ev_bseqr: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abseq r s t1 t2) e ->
    copland_compile t2 {| st_ev := splitEv_r s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t2 (splitEvr s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eassumption.
    eassumption.
    apply abseq_subr.
    eassumption.
  -
    destruct s.
    destruct s; destruct s0; ff.
    +
      split; eauto.

      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abseq_subr.
      eassumption.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
    +
      split; eauto.

      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abseq_subr.
      eassumption.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
Defined.

Lemma sig_term_ev_bparl: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abpar r s t1 t2) e ->
    copland_compile t1 {| st_ev := splitEv_l s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t1 (splitEvl s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eassumption.
    eassumption.
    apply abpar_subl.
    eassumption.
  -
    destruct s.
    destruct s; destruct s0; ff.
    +
      split; eauto.

      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abpar_subl.
      eassumption.
    +
      split; eauto.

      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abpar_subl.
      eassumption.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
Defined.

Lemma sig_term_ev_bparr: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abpar r s t1 t2) e ->
    copland_compile t2 {| st_ev := splitEv_r s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t2 (splitEvr s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eassumption.
    eassumption.
    apply abpar_subr.
    eassumption.
  -
    destruct s.
    destruct s; destruct s0; ff.
    +
      split; eauto.
      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abpar_subr.
      eassumption.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
    +
      split; eauto.

      unfold not.
      intros.
      destruct_conjs.
      invc H5.
      eapply H3.
      eassumption.
      econstructor.
      apply abpar_subr.
      eassumption.
    +
      split.
      ++
        cbv.
        intros.
        invc H5.
        destruct_conjs.
        invc H9.
      ++
        intros.
        invc H4.
        destruct_conjs.
        subst.
        invc H8.
Defined.

Lemma hshsig_ev_term_contra: forall t p (e e' :EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
    wf_ec ecc ->
    not_hash_sig_term_ev t e ->
    
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->

    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    not_hash_sig_ev e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; repeat ff.
  -
    jkjke'.
    ff.
    unfold not_hash_sig_term_ev in *.
    destruct_conjs.
    eassumption.
  -
    unfold cons_uu in *.
    ff.
    ff.
    assert (not_hash_sig_ev e2).
    {
      eapply not_ev; eauto.
    }

    eapply not_hshsig_uuc; eauto.
  -
    repeat ff.
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    }
    rewrite fold_recev in *.
    assert ((evc (get_bits ecc) (get_et ecc)) = ecc).
    {
      destruct ecc.
      ff.
    }
    
    rewrite H4 in *; clear H4.
    jkjke'.
    ff. 
    eapply not_hshsig_ggc; eauto.
  -
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    }

    assert (~ (gg_sub e)).
    {
      cbv in H1.
      destruct_conjs.
      unfold not; intros.
      invc H6.
      destruct_conjs.
      subst.
      eapply H5.
      repeat eexists.
      eassumption.
      repeat eexists.
      econstructor.
    }
    unfold not in *.

    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    eapply H4.
    invc H5.
    destruct_conjs.
    subst.
    invc H6.

    eapply gg_recons; eauto.

    ff.

    edestruct hh_recons.
    eassumption.
    eassumption.

    unfold not_hash_sig_ev in H3.
    unfold not in *.
    exfalso.
    eapply H3.
    econstructor.
    repeat eexists.
    eassumption.
    eassumption.

  - (* aatt case *)
    do_wf_pieces.
    assert (not_hash_sig_term_ev t e).
    {
      invc H1.
      destruct_conjs.
      econstructor.
      cbv.
      intros.
      destruct_conjs.
      subst.
      unfold not_hash_sig_term in H5.
      unfold not in H5.
      eapply H5 with (t':=(alseq (n2, n3) H9 H7)).
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.
      eapply termsub_transitive.
      eassumption.
      econstructor.
      econstructor.
      split.
      eassumption.
      unfold not in *.
      intros.
      destruct_conjs.
      eapply H6.
      eassumption.
      invc H8.
      econstructor.
      eapply termsub_transitive.
      eassumption.
      econstructor.
      econstructor.
    }
    
    eapply IHt.
    eassumption.
    2: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
  -
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.

    ff.
    destruct ecc; destruct st_ev.
    
    assert (not_hash_sig_term_ev t1 e).
    eapply sig_term_ev_lseq; eauto.

    assert (not_hash_sig_ev H9).
    {
      eapply IHt1.
      eassumption.
      2: { eassumption. }
      2: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
    }

    assert (not_hash_sig_term t2). (* TODO: make this an auto lemma *)
    {
      unfold not_hash_sig_term_ev in H1.
      destruct_conjs.
      unfold not_hash_sig_term in H1.
      cbv.
      unfold not in H1.
      intros.
      destruct_conjs.
      eapply H1 with (t':= (alseq (n, n0) H20 H18)).
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.
      subst.
      apply alseq_subr.
      eassumption.
    }

    assert (not_hash_sig_term_ev t2 H9).
    {
      split.
      eassumption.
      split.
      eassumption.
      intros.
      unfold not.
      intros.

      assert (gg_sub e \/
              (exists r, term_sub (aasp r SIG) t1)).
      {
        eapply sig_is.
        eassumption.
        2: { eassumption. }
        eassumption.
        eassumption.
        eassumption.
        eassumption.
      }
      door.
      +
        unfold not_hash_sig_term_ev in H1.
        destruct_conjs.
        unfold not in H21.
        eapply H21.
        eassumption.
        invc H18.
        econstructor.
        apply alseq_subr.
        eassumption.
      +
        invc H18.
        unfold not_hash_sig_term_ev in H1.
        destruct_conjs.
        unfold not_hash_sig_term in H1.
        unfold not in H1.
        eapply H1 with (t':= (alseq r t1 t2)).
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.
        econstructor.
    }
    
    eapply IHt2.
    eassumption.
    2: { eassumption. }
    2: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
  - (* abseq case *)
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    repeat find_rewrite.

    clear H11; clear H12.
    jkjke'.
    jkjke'.
    vmsts.
    ff.
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    invc H11.
    +
      invc H2.
      destruct_conjs.
      invc H14.
    +
      rewrite fold_recev in *.
      do_wfec_preserved.
      do_somerecons.
      assert (not_hash_sig_ev H11).
      {
        eapply IHt1.
        eassumption.
        
        4: { eassumption. }
        4: {
          eassumption. }
        eassumption.
        assert (not_hash_sig_term_ev t1 (splitEvl s H5)).
        {
          destruct ecc.
          eapply sig_term_ev_bseql.
          eassumption.
          eassumption.
          eassumption.
        }
        eassumption.
        destruct s; destruct s; destruct s0; ff.

      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H22.
      unfold not in *.
      eapply H22.
      econstructor.
      repeat eexists.
      eassumption.
      jkjke'.
      jkjke'.
      jkjke'.
      jkjke'.
      repeat ff.

    +
      rewrite fold_recev in *.
      assert (not_hash_sig_ev e5).
      {
        eapply IHt2.
        eassumption.
        
        4: { symmetry. eassumption. }
        4: {
          eassumption. }
        eassumption.
        assert (not_hash_sig_term_ev t2 (splitEvr s H5)).
        {
          destruct ecc.
          eapply sig_term_ev_bseqr.
          eassumption.
          eassumption.
          eassumption.
        }
        eassumption.
        destruct s; destruct s; destruct s0; ff.

      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H11.
      unfold not in *.
      eapply H11.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.

  - (* abpar case *)
    
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    repeat find_rewrite.

    clear H11; clear H12.
    jkjke'.
    jkjke'.
    vmsts.
    ff.
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    invc H11.
    +
      invc H2.
      destruct_conjs.
      invc H14.
    +
      rewrite fold_recev in *.
      do_wfec_preserved.
      do_somerecons.
      assert (not_hash_sig_ev H11).
      {
        eapply IHt1.
        eassumption.
        
        4: { eassumption. }
        4: {
          eassumption. }
        eassumption.
        assert (not_hash_sig_term_ev t1 (splitEvl s H5)).
        {
          destruct ecc.
          eapply sig_term_ev_bparl.
          eassumption.
          eassumption.
          eassumption.
        }
        eassumption.
        destruct s; destruct s; destruct s0; ff.

      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H22.
      unfold not in *.
      eapply H22.
      econstructor.
      repeat eexists.
      eassumption.
      jkjke'.
      jkjke'.
      jkjke'.
      jkjke'.
      repeat ff.

    +
      rewrite fold_recev in *.
      assert (not_hash_sig_ev e5).
      {
        eapply IHt2.
        eassumption.
        
        4: { symmetry. eassumption. }
        4: {
          eassumption. }
        eassumption.
        assert (not_hash_sig_term_ev t2 (splitEvr s H5)).
        {
          destruct ecc.
          eapply sig_term_ev_bparr.
          eassumption.
          eassumption.
          eassumption.
        }
        eassumption.
        destruct s; destruct s; destruct s0; ff.
      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H11.
      unfold not in *.
      eapply H11.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.
Defined.

Lemma sig_term_ev_lseqr: forall r t1 t2 e e0 e1 e2 e3 tr tr' p p' H5,
    well_formed_r t1 ->
    wf_ec (evc e0 e1) ->
    not_hash_sig_term_ev (alseq r t1 t2) e ->
    copland_compile t1 {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |}) ->
    Some e  = reconstruct_ev (evc e0 e1) ->
    Some H5 = reconstruct_ev (evc e2 e3) ->
    not_hash_sig_term_ev t2 H5.
Proof.
  intros.

  assert (not_hash_sig_term_ev t1 e).
  eapply sig_term_ev_lseq; eauto.

  split.
  -
    invc H1.
    do_not_hshsig.
    eassumption.
  -
    split.
    +
      eapply hshsig_ev_term_contra.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
    +

      intros.
      unfold not; intros.

      edestruct sig_is.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.


      unfold not_hash_sig_term_ev in H1.
      destruct_conjs.
      unfold not_hash_sig_term in H1.
      unfold not in *.
      invc H8.
      eapply H11.
      eassumption.
      econstructor.
      apply alseq_subr.
      eassumption.

      destruct_conjs.
      unfold not_hash_sig_term_ev in H1.
      destruct_conjs.
      unfold not_hash_sig_term in H1.
      unfold not in *.
      invc H8.
      eapply H1.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.
      econstructor.
Defined.

Ltac do_evsub_ihhh' :=
  match goal with
  | [H: copland_compile ?t1
                        {| st_ev := ?ee; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
        (* H2: copland_compile ?t2
                            {| st_ev := _(*?stev'*); st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}), *)
        H3: Some _ = reconstruct_ev ?ee,
            H4: Some ?v' = reconstruct_ev ?stev,
                IH: forall _, _ -> _ ,(*context[forall _, well_formed_r ?t1 -> _], *)
       Hf: well_formed_r ?t1,
       Hnn: not_none_none ?t1,
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
                   

       |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') _) \/
          (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
              EvSub (hhc p'0 bs ett) _ /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
            (*context[EvSub _(*(uuc ?i ?args ?tpl ?tid ?n _)*) _ \/ _]*)
    ] => 

    

    assert_new_proof_by 
      (
        (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') v') \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) v' /\ EvSubT (uu i args tpl tid et') ett)
      )

      (*
          assert_new_proof_by
            (exists ee, EvSub (uuc i args tpl tid n ee) v \/
             (exists (ett : Evidence) (p'0 bs : nat) (et':Evidence),
                 EvSub (hhc p'0 bs ett) v /\ EvSubT (uu i args tpl tid et') ett)) 
       *)
      ltac: (eapply IH; [apply Hf | apply Hnn| apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
              (*ltac:(ff; repeat jkjke'; eauto)*)
              
              
  end.

Lemma uu_preserved': forall t p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc',

    well_formed_r t ->
    not_none_none t ->
    wf_ec ecc ->
    Some e = (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->
    events t p et (umeas n p0 i args tpl tid) ->
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett)
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
    +
      inv_events.
      ff.
      unfold cons_uu in *.
      repeat ff.
      left.
      eexists.
      econstructor.
  -
    ff.
    invEvents.
    do_wf_pieces.
    do_not_none.

    eapply IHt; eauto.
    apply copland_compile_at; eauto.
  -
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.

      repeat do_evsub_ihhh'.

      door.
      ++
        destruct_conjs.

        repeat jkjke'.
        repeat ff.

        do_evaccum.

        (*
        clear H12. *)
        door.
        +++
          left.
          eauto.
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).

      ++
        repeat jkjke'.
        repeat ff.
        
        do_evaccum.

        door.
        +++
          right.
          repeat (eexists; eauto).
        +++
          destruct_conjs.
          ff.
          right.
          repeat eexists.
          eauto.

          eapply evsubT_transitive.
          eapply hhSubT.
          eassumption.
          eassumption.
          
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      do_wfec_preserved.
      do_somerecons.

      repeat do_evsub_ihhh'.

      clear H17.
      door.
      ++
        eauto.
      ++
        destruct_conjs;
          right;
          repeat (eexists; eauto).


  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        do_evsub_ihhh';

        door; repeat jkjke'; ff;
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).

  - (* abpar case *)
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        do_evsub_ihhh';

        door; repeat jkjke'; ff;
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
Defined.


Lemma uu_preserved: forall t1 t2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'' ecc,
    well_formed_r t1 ->
    well_formed_r t2 ->
    not_none_none t1 ->
    not_none_none t2 ->
    wf_ec e ->
    Some e' = (reconstruct_ev ecc) ->
    events t1 p et (umeas n p0 i args tpl tid) ->
    copland_compile t1 {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |}) ->
    
    copland_compile t2
                    {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |} =
    (Some tt, {| st_ev := ecc; st_trace := tr'; st_pl := p'' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett)
    ).
Proof.
  intros.

  ff.
  do_wfec_preserved.
  do_somerecons.
  
  assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') H11) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H11 /\
          EvSubT (uu i args tpl tid et') ett)
    ).
  {
    eapply uu_preserved'.
    apply H.
    eassumption.
    4: { eassumption. }
    4: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
  }
  door;
    do_evaccum.
  +
    
    clear H18.
    door; eauto.

    right;
      (repeat eexists; eauto).
  +
    clear H22.
    door; ff.
    ++
      right;
        repeat (eexists; eauto).

    ++
      assert (EvSubT (uu i args tpl tid H19) H22).
      {
        eapply evsubT_transitive.
        apply hhSubT.
        eassumption.
        eassumption.
      }
      
      right; 
        repeat (eexists; eauto).
Defined.

Ltac sigEventFacts :=
  match goal with
  | [H: sigEvent _ _ _ _ |- _] => invc H
  end.

Ltac sigEventPFacts :=
  match goal with
  | [H: sigEventP _ |- _] => invc H
  end.

Lemma gg_preserved': forall t p et n p0 et'
                       tr e e' tr' p' bits ecc',

    well_formed_r t ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    wf_ec (evc bits et) ->
    Some e = (reconstruct_ev (evc bits et)) ->
    Some e' = (reconstruct_ev ecc') ->
    events t p et (sign n p0 et') ->
    copland_compile t {| st_ev := (evc bits et); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (
      (exists bits e'', EvSub (ggc p0 (do_sig (MonadVM.encodeEv (evc bits et')) p0) e'') e' /\
                   et_fun e'' = et'
      )
    ).
Proof.

  intros.
  generalizeEverythingElse t.
  
  induction t; intros.
  -
    subst.
    destruct a; try (ff; tauto).
    +
      ff.
      invEvents.
      ff.

      repeat eexists.
      econstructor.
      rewrite fold_recev in *.
      symmetry.
      
      eapply etfun_reconstruct; eauto.

  -
    ff.
    invEvents.
    do_wf_pieces.
    do_not_none.
    invc H1.
    
    do_not_hshsig.

    eapply IHt; eauto.
    econstructor.
    eassumption.
    split; try eassumption.
    intros.
    unfold not in *; intros.
    invc H11.
    eapply H9.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
    apply copland_compile_at; eauto.
  -
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.

      assert (not_hash_sig_ev H12).
      {
        destruct st_ev.
        eapply hshsig_ev_term_contra.
        apply H7.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_lseq.
        eassumption.
        eassumption.
        eassumption.
        eassumption.       
      }
      
      destruct st_ev.
      edestruct IHt1.
      eassumption.
      eassumption.
      eapply sig_term_ev_lseq; eassumption.
      4: { eassumption. }
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.

      destruct_conjs.

      repeat jkjke'.
      repeat ff.
      repeat jkjke'.
      repeat ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.

      do_evaccum.

      door.
      +++
        eauto.
      +++
        ff.
        assert (not_hash_sig_ev H11).
        {      
          destruct ecc'.
          eapply hshsig_ev_term_contra.
          apply H8.
          4: { eassumption. }
          4: { eassumption. }
          eassumption.
          2: { eassumption. }

          eapply sig_term_ev_lseqr.
          apply H7.
          3: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          eassumption.
        }

        unfold not_hash_sig_ev in H24.
        specialize H24 with (e':=(hhc H4 H21 H3)).
        unfold not in *.
        exfalso.
        apply H24.
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.       
        
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      do_wfec_preserved.
      do_somerecons.
      destruct st_ev.
      destruct ecc'.

      assert (e1 = (aeval t1 p et)).
      {
        rewrite <- eval_aeval.
        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.

      edestruct IHt2.
      eassumption.
      eassumption.
      eapply sig_term_ev_lseqr.
      apply H7.
      3: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.
      2: { eassumption. }
      2: { eassumption. }
      eassumption.

      repeat jkjke'; repeat ff.
      repeat jkjke'; repeat ff.
      
  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        try do_evsub_ihhh'.

    +
      

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {
        
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H7.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.       
      }

      assert (not_hash_sig_ev e5).
      {
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.      
      }
      
      destruct s; destruct s; destruct s0; ff.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: { eassumption. }
        eassumption.

        destruct_conjs.
        eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: {
          eassumption. }
        eassumption.

        destruct_conjs.
        eauto.

      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.
        
        destruct_conjs.
        eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.
        
        destruct_conjs.
        eauto.

    +

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {
        
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H7.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.       
      }

      assert (not_hash_sig_ev e5).
      {
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.      
      }
      
      destruct s; destruct s; destruct s0; ff.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: {
          eassumption. }
        eassumption.

        destruct_conjs.
        eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.
        
        destruct_conjs.
        eauto.
      ++  
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: {
          eassumption. }
        eassumption.

        destruct_conjs.
        eauto.


      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.

        destruct_conjs.
        eauto.

  - (* abpar case *)
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        try do_evsub_ihhh'.

    +
      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {
        
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H7.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.
        
      }

      assert (not_hash_sig_ev e5).
      {
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.
        
      }
      

      destruct s; destruct s; destruct s0; ff.
      ++
        
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: {
          eassumption. }
        eassumption.

        destruct_conjs.
        eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: {
          eassumption. }
        eassumption.

        destruct_conjs.
        eauto.

      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.
        
        destruct_conjs.
        eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.
        
        destruct_conjs.
        eauto.

    +
      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {    
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H7.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.     
      }

      assert (not_hash_sig_ev e5).
      {
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        4: { eassumption. }
        4: { eassumption. }
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        eassumption.
        eassumption.
        destruct s.
        destruct s; destruct s0; ff.    
      }
      

      destruct s; destruct s; destruct s0; ff.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: { eassumption. }
        eassumption.

        destruct_conjs.
        eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.
        
        destruct_conjs.
        eauto.

      ++  
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        2: { eassumption. }
        eassumption.
        2: {
          eassumption. }
        eassumption.

        destruct_conjs.
        eauto.

      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        eassumption.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        ff.
        eassumption.
        
        destruct_conjs.
        eauto.
Defined.
