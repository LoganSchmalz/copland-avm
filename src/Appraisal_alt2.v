Require Import Maps Event_system Term_system MonadVM ConcreteEvidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import StAM Appraisal_Defs Impl_appraisal (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Require Import Lia.

Set Nested Proofs Allowed.

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

Lemma evsubT_transitive: forall e e' e'',
    EvSubT e e' ->
    EvSubT e' e'' ->
    EvSubT e e''.
Proof.
  intros.
  generalizeEverythingElse e''.
  induction e''; intros;
    try evSubTFacts;
       eauto.
Defined.

Lemma evsub_etfun: forall e e',
    EvSub e e' ->
    EvSubT (et_fun e) (et_fun e').
Proof.
  intros.
  induction H; intros;
    ff; eauto.
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

Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall ls et,
    length ls = et_size et ->
    wf_ec (evc ls et).

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
    end.

Ltac find_wfec' :=
  repeat 
    let tac H H2 H3 H4 := eapply H; [apply H2 | apply H3 | apply H4] in
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
        
        ltac: (tac H H2 H3 H4)
    (*
                     ltac:(eapply H; [apply H2 | apply H3 | apply H4]) *)
    end.

Ltac find_wfec'' :=
  repeat
    let tac H H2 H4 := (eapply H with (e:=evc [0] mt); [apply H2 | econstructor; tauto | apply H4]) in
    match goal with
    | [H: context [well_formed_r ?t -> _](*
                   wf_ec _ ->
                   copland_compile _ _ _ = _ ->
                   wf_ec _]*),
          H2: well_formed_r ?t,
              H4: copland_compile ?t
                                  {| st_ev := _; st_trace := _; st_pl := _ |} =
                  (_, {| st_ev := ?e'; st_trace := _; st_pl := _ |})
                    


       |- _ ] => 
      assert_new_proof_by
        (wf_ec (e'))
        
        ltac: (tac H H2 H4)
    (*
                     ltac:(eapply H; [apply H2 | apply H3 | apply H4]) *)
    end.

Ltac find_wfec := find_wfec'; find_wfec''.

Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
    end.

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
    (*
    rewrite H3. *)
    eapply IHt1;
      try eassumption.

    apply copland_compile_at;
      try eassumption.
  -
    repeat ff.
    vmsts.
    do_wf_pieces.
    (*
    eapply IHt1_2.
    eassumption.
    2: eassumption.
    eauto. *)
  -
    repeat ff; vmsts; repeat ff; subst.
    do_wf_pieces.

    destruct s;
      ff;
      unfold mt_evc in *;
      find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.
  -
    repeat ff; vmsts; repeat ff; subst.
    do_wf_pieces.

    destruct s;
      ff;
      unfold mt_evc in *;
      find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.    


(*
    
    +
      ff.
      unfold mt_evc in *.
      find_wfec.
      inv_wfec.

      (*
      Set Ltac Backtrace.

      fail_if_in_hyps_type (wf_ec (evc e e0; assert H by tac
      find_wfec.
      Info Level 1.

      Info 33 find_wfec.
      find_wfec.
      Ltac Debug. *)


      (*
      
      invc H3.

      find_wfec.

      assert (wf_ec (evc e1 e2)).
      {
        eapply IHt1_2.
        eassumption.
        2: { eassumption. }
        econstructor. tauto.
      }
      invc H3. *)

      
      econstructor.
      ff.
      repeat jkjke'.

      (*
      rewrite <- H5.
      rewrite <- H6.
      Search (length (_ ++ _)). *)
      eapply app_length.
    +
       ff.
      unfold mt_evc in *.
      assert (wf_ec (evc e e0)).
      {
        eapply IHt1_1.
        eassumption.
        2: { eassumption. }
        econstructor. tauto.
      }
      
      invc H3.

      assert (wf_ec (evc e1 e2)) by eauto.
      invc H3.
      econstructor.
      ff.
      rewrite <- H5.
      rewrite <- H6.
      eapply app_length.
    +
      ff.
      assert (wf_ec (evc e e0)) by eauto.
      invc H3.

      assert (wf_ec (evc e1 e2)) by eauto.
      invc H3.
     
      econstructor.
      ff.
      rewrite <- H5.
      rewrite <- H6.
      eapply app_length.
 *)


    (*
    -

    repeat ff.
    vmsts.
    repeat ff.
    subst.
    do_wf_pieces.

    destruct s.
    +
      ff.
      unfold mt_evc in *.
      assert (wf_ec (evc e e0)) by eauto.
      invc H3.

      assert (wf_ec (evc e1 e2)).
      {
        eapply IHt1_2.
        eassumption.
        2: { eassumption. }
        econstructor. tauto.
      }
      invc H3.
      econstructor.
      ff.
      rewrite <- H5.
      rewrite <- H6.
      Search (length (_ ++ _)).
      eapply app_length.
    +
       ff.
      unfold mt_evc in *.
      assert (wf_ec (evc e e0)).
      {
        eapply IHt1_1.
        eassumption.
        2: { eassumption. }
        econstructor. tauto.
      }
      
      invc H3.

      assert (wf_ec (evc e1 e2)) by eauto.
      invc H3.
      econstructor.
      ff.
      rewrite <- H5.
      rewrite <- H6.
      eapply app_length.
    +
      ff.
      assert (wf_ec (evc e e0)) by eauto.
      invc H3.

      assert (wf_ec (evc e1 e2)) by eauto.
      invc H3.
     
      econstructor.
      ff.
      rewrite <- H5.
      rewrite <- H6.
      eapply app_length. *)
Defined.

Lemma peel_fact': forall e x y H,
    length e = S x ->
    peel_bs e = Some (y, H) ->
    length H = x.
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.

Lemma peel_fact: forall e x y H et,
    length e = S x ->
    peel_bs e = Some (y, H) ->
    et_size et = x ->
    wf_ec (evc H et).
Proof.
  intros.
  econstructor.
  eapply peel_fact'; eauto.
  lia.
Defined.

Lemma firstn_long: forall (e:list BS) x,
    length e >= x ->
    length (firstn x e) = x.
Proof.
  intros.
  eapply firstn_length_le.
  lia.
Defined.

Lemma skipn_long: forall (e:list BS) x y,
    length e = x + y ->
    length (skipn x e) = y.
Proof.
  intros.
  assert (length (skipn x e) = length e - x).
  { eapply skipn_length. }
  lia.
Defined.

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

Ltac door :=
  match goal with
  | [H: _ \/ _  |- _] =>
    destruct H
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

Lemma evAccum: forall t p (e e' e'':EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
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
      right.
      repeat eexists.
      econstructor.
      Check evsub_etfun.
      assert (e1 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.

      apply evsub_etfun; eauto.
  - (* aatt case *)
    do_wf_pieces.
    ff.
    
    eapply IHt.
    eassumption.
    apply H0.
    eassumption.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
  - (* alseq case *)
    ff.
    dosome.
    vmsts.

    do_wf_pieces.

    do_wfec_preserved.

    do_somerecons.

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
  -
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
    
    rewrite H9 in *; clear H9.
    rewrite H10 in *; clear H10.

    do_wfec_preserved.

    do_somerecons.

    destruct s;
    
      ff;
        try unfold mt_evc in *;
        repeat jkjke';
        ff;
        rewrite fold_recev in *;
        do_evsub_ih;
      
        ff;
       
        door; destruct_conjs;
          try eauto;
          try (right; repeat (eexists; eauto)).

  -
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
 
    rewrite H9 in *; clear H9.
    rewrite H10 in *; clear H10.

    do_wfec_preserved.

    do_somerecons.

        destruct s;
    
      ff;
        try unfold mt_evc in *;
        repeat jkjke';
        ff;
        rewrite fold_recev in *;
        do_evsub_ih;
      
        ff;
       
        door; destruct_conjs;
          try eauto;
          try (right; repeat (eexists; eauto)).
Defined.


Ltac do_evsub_ih' :=
  match goal with
  | [H: copland_compile ?t1
                        {| st_ev := _; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
        H2: copland_compile ?t2
                            {| st_ev := _(*?stev'*); st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?v = reconstruct_ev ?stev

     |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') _) \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) _ /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
          (*context[EvSub _(*(uuc ?i ?args ?tpl ?tid ?n _)*) _ \/ _]*)
    ] =>

    assert_new_proof_by 
      (
        (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') v) \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) v /\ EvSubT (uu i args tpl tid et') ett)
      )

      (*
          assert_new_proof_by
            (exists ee, EvSub (uuc i args tpl tid n ee) v \/
             (exists (ett : Evidence) (p'0 bs : nat) (et':Evidence),
                 EvSub (hhc p'0 bs ett) v /\ EvSubT (uu i args tpl tid et') ett)) 
       *)
      eauto
      (*ltac:(ff; repeat jkjke'; eauto)*)
  end.

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
                               (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
    end.

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
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
       

     |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') (ssc ?v' _)) \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) (ssc ?v' _) /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
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
      ltac: (eapply IH; [apply Hf | apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
      (*ltac:(ff; repeat jkjke'; eauto)*)
       
      
  end.

Ltac do_evsub_ihhh'r :=
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
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
       

     |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') (ssc _ ?v')) \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) (ssc _ ?v') /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
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
      ltac: (eapply IH; [apply Hf | apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
      (*ltac:(ff; repeat jkjke'; eauto)*)
       
      
  end.

Ltac do_evsub_ihhh'p :=
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
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
       

     |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') (ppc ?v' _)) \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) (ppc ?v' _) /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
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
      ltac: (eapply IH; [apply Hf | apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
      (*ltac:(ff; repeat jkjke'; eauto)*)
       
      
  end.

Ltac do_evsub_ihhh'pr :=
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
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
       

     |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') (ppc _ ?v')) \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) (ppc _ ?v') /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
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
      ltac: (eapply IH; [apply Hf | apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
      (*ltac:(ff; repeat jkjke'; eauto)*)
       
      
  end.

Lemma uu_preserved': forall t p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc',

    well_formed_r t ->
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

    eapply IHt; eauto.
    apply copland_compile_at; eauto.
  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)

      
      do_wfec_preserved.
      do_somerecons.

      do_evsub_ih'.

      door.
      ++
        destruct_conjs.

        repeat jkjke'.
        repeat ff.

        do_evaccum.
         
        clear H12.
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

      repeat do_evsub_ih'.

      clear H14.
      door.
      ++
        destruct_conjs.
        left.
        eauto.
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
     
  - (* abseq case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)


      do_wfec_split.

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      rewrite H8 in *; clear H8.
      rewrite H9 in *; clear H9.

      do_wfec_preserved.

      do_somerecons.
      
    destruct s.
    ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'.

      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

            ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'.

      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

            ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'.

      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
   
    + (* t2 case *)


      do_wfec_split.

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      rewrite H8 in *; clear H8.
      rewrite H9 in *; clear H9.
      
      do_wfec_preserved.

      do_somerecons.

      repeat do_pl_immut.
      subst.


    destruct s.
    ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'r.
      
      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

    ++

      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_evsub_ihhh'r.
      
      repeat ff.
        
      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

    ++
      

      ff.
      repeat 
      jkjke'.
      ff.
      rewrite fold_recev in *.

      do_evsub_ihhh'r.
      
      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
      


  - (* abpar case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)

      do_wfec_split.

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      rewrite H8 in *; clear H8.
      rewrite H9 in *; clear H9.

      do_wfec_preserved.

      do_somerecons.
      
    destruct s.
    ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'p.

      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

            ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'p.

      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

            ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'p.

      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
   
    + (* t2 case *)


      do_wfec_split.

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      rewrite H8 in *; clear H8.
      rewrite H9 in *; clear H9.

      do_wfec_preserved.

      do_somerecons.

      repeat do_pl_immut.
      subst.


    destruct s.
    ++
      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_somerecons.

      do_evsub_ihhh'pr.

      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

    ++

      ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
   
      unfold mt_evc in *.

      do_evsub_ihhh'pr.
      
      repeat ff.
        
      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).

    ++
      

      ff.
      repeat 
      jkjke'.
      ff.
      rewrite fold_recev in *.
      
      do_evsub_ihhh'pr.
      
      ff.

      door.
      +++
        eauto.
      +++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
Defined.


Lemma uu_preserved: forall t1 t2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'' ecc,
    well_formed_r t1 ->
    well_formed_r t2 ->
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
      (exists e'', EvSub (uuc i args tpl tid n e'') H9) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H9 /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      4: { eassumption. }
      4: { eassumption. }
      eassumption.
      
      eassumption.
      eassumption.
    }
  generalizeEverythingElse e'.
  induction e'; intros.

  -

    door.
    +  

      do_evaccum.

      door.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
    +
      do_evaccum.
       door.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.

  - (* nnc case *)
    
    door.

    +
      destruct_conjs.

      do_evaccum.

      door.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
    +
      destruct_conjs.

      do_evaccum.
      door.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
      
  - (* uuc case *)

    door.
    +
      destruct_conjs.

      do_evaccum.
      
      door.
      ++
        eauto.
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +

      do_evaccum.
      
       door.
      ++
        invc H21.
        right.
        repeat eexists.
        apply uuSub.
        eassumption.
        eassumption.
      ++
        destruct_conjs.
        ff.
        invc H24.
        Print do_hh_sub.
        Print do_evsubh_ih.
        
        assert (EvSubT (uu i args tpl tid H17) H21).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        
        right.
        repeat eexists.
        apply uuSub.
        eassumption.
        eassumption.


  - (* ggc case *)

    door.
    +

      do_evaccum.
      door.
      ++
        eauto.
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +

      do_evaccum.
       door.
      ++
        invc H21.
        right.
        repeat eexists.
        apply ggSub.
        eassumption.
        eassumption.
      ++
        destruct_conjs.
        ff.
        invc H24.
        assert (EvSubT (uu i args tpl tid H17) H21).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        
        right.
        repeat eexists.
        apply ggSub.
        eassumption.
        eassumption.     

  - (* hhc case *)
    
    door.
    +
      do_evaccum.

      door.
      ++
        eauto.
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      do_evaccum.

       door.
      ++
        invc H21.
        right.
        repeat eexists.
        eauto.
        eauto.
      ++
        destruct_conjs.
        ff.
        invc H24.
        assert (EvSubT (uu i args tpl tid H17) e).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        
        right.
        repeat eexists.
        eauto.
        eauto.



  - (* ssc case *)

    door.

    +
      do_evaccum.
      door.
      ++
        eauto.

      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      do_evaccum.

       door.
      ++
        invc H21.
        +++
        right.
        repeat eexists.
        apply ssSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ssSubr.
          eassumption.
          eassumption.
      ++
        destruct_conjs.
        ff.
        assert (EvSubT (uu i args tpl tid H17) H21).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        invc H24.
        +++
        
        
        right.
        repeat eexists.
        apply ssSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ssSubr.
          eassumption.
          eassumption.

  - (* ppc case *)

    door.
    +
      do_evaccum.

      door.
      ++
        eauto.
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      do_evaccum.

       door.
      ++
        invc H21.
        +++
        right.
        repeat eexists.
        apply ppSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ppSubr.
          eassumption.
          eassumption.
      ++
        destruct_conjs.
        ff.
        assert (EvSubT (uu i args tpl tid H17) H21).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        invc H24.
        +++
        
        
        right.
        repeat eexists.
        apply ppSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ppSubr.
          eassumption.
          eassumption.
Defined.

Definition get_et (e:EvC) : Evidence :=
  match e with
  | evc ec et => et
  end.
    


Lemma appraisal_correct : forall t e' tr tr' p p' ecc ev ee,
    well_formed_r t ->
    wf_ec ee(*(evc bits et)*) ->
    (*Ev_Shape e et -> *)
    Some e' = (reconstruct_ev ecc) -> (*fromSome mtc (reconstruct_ev ecc) ->*) (* = (Some e') -> *)
    copland_compile t
      {| st_ev := ee; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc;
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p (get_et ee) ev ->
    
    (*build_app_comp_evC e' = app_res /\ *)
    appEvent_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    measEventFacts.
    evEventFacts.
    destruct ee.
    inv_events.
    ff.
    break_match; try solve_by_inversion.
    invc H1.
    (*
    assert (exists x, reconstruct_ev' bits et = Some x).
    {
      admit.
    }
    destruct_conjs.
    
    rewrite H1.
     *)
    
    repeat econstructor.

  - (* aatt case *)
    measEventFacts.
    evEventFacts.
    invEvents.
    vmsts.
    ff.
    do_wf_pieces.
    eapply IHt.
    eassumption.
    eassumption.
    eassumption.

    eapply copland_compile_at.
    eassumption.
    econstructor.
    eassumption.
    econstructor.
  - (* alseq case *)
    edestruct wf_lseq_pieces;[eauto | idtac].
    (* do_wf_pieces. *)
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    measEventFacts.
    do_pl_immut.
    do_pl_immut.
    subst.

    invc H6.

    
    inv_events.
     + (* t1 case *)
       (*clear H0. *)

       edestruct uu_preserved.
       apply H4.
       apply H5.
       5: { eassumption. }
       4: { eassumption. }
       eassumption.
       jkjke'.
       eauto.

       (*

       assert (
           (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
           (exists ett p' bs et',
               EvSub (hhc p' bs ett) e' /\
               EvSubT (uu i args tpl tid et') ett)
         ).
              
       {
         Check uu_preserved.
         eapply uu_preserved with (st_ev := st_ev) (e':=e').
         apply H4.
         apply H5.
         5: { eassumption. }
         4: { eassumption. }
         eassumption.
         jkjke'.
         eauto.

       }
       destruct H3.
       ++ *)

       destruct_conjs.



       assert (
        exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                     (build_app_comp_evC (fromSome mtc (reconstruct_ev ecc)))).
       {
         eapply uuc_app; 
         jkjke'.
       }
       destruct_conjs.
       econstructor.
       jkjke'.
       destruct_conjs.
       eapply ahuc.
       eassumption.
       eapply hhc_app; eauto.



       (*
       rewrite <- H1 in *.
       eassumption.
       ++
         rewrite <- H1 in *.
         ff.
         destruct_conjs.

         eapply ahuc.
         eassumption.
         (*
         apply H9. *)
         eapply hhc_app; eauto.
         (*

         assert (EvSub (hhc H2 (checkHash H1 H2 H5) H1) (build_app_comp_evC (fromSome mtc (reconstruct_ev ecc)))).
         {
           eapply hhc_app; eauto.
         }

         eapply ahuc.
         eassumption.
         eassumption. *)

        *)
       
     + (* t2 case *)

       do_wfec_preserved.
       destruct ecc.
       destruct st_ev.
       


       
       eapply IHt2.
       eassumption.
       3: { eassumption. }
       eassumption.
       eassumption.
       econstructor.
       destruct ee.
       ff.
       assert (e2 = aeval t1 p e4).
         {
           rewrite <- eval_aeval.
           
           eapply cvm_refines_lts_evidence.
           eassumption.
           eassumption.
         }
         subst.
         eassumption.
         econstructor.



         (*
       


       
       assert (appEvent_EvidenceC (umeas n p0 i args tpl tid)
                                  (build_app_comp_evC (e'))).
       {
         destruct ecc.
         destruct st_ev.
         eapply IHt2.
         eassumption.
         3: { eassumption. }

         eapply wf_ec_preserved_by_cvm.
         apply H4.
         eassumption.
         eassumption.
         eassumption.
         
         (*
         
         
         2: {
           eassumption.
         }      
         eapply cvm_refines_lts_evidence.
         apply H3.
         eassumption.
         eassumption.
         tauto. *)
         econstructor.
         Check eval_aeval.
         assert (e2 = aeval t1 p et).
         {
           rewrite <- eval_aeval.
           
           eapply cvm_refines_lts_evidence.
           eassumption.
           eassumption.
         }
         subst.
         eassumption.
         econstructor.
       }
       eassumption.
       
         (*
         
         rewrite eval_aeval.
         eassumption. 
         econstructor.
       }
       eassumption. *)

          *)
         
    - (* abseq case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bseq_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    (*

    assert (exists x, reconstruct_ev' (firstn (et_size e0) (e ++ e1)) e0 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H1. 

    assert (exists x, reconstruct_ev' (skipn (et_size e0) (e ++ e1)) e2 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H6.
     *)
    
    
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    rewrite H9 in *; clear H9.
    rewrite H8 in *; clear H8.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)

    assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
    {
        
        
        destruct ee; ff.
        destruct s; ff.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
    }

    invc H8.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.

    + (* t1 case *)

    assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
    {
        
        
        destruct ee; ff.
        destruct s; ff.
        ++
          rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
    }

    invc H8.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.

    - (* abpar case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bpar_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    (*

    assert (exists x, reconstruct_ev' (firstn (et_size e0) (e ++ e1)) e0 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H1. 

    assert (exists x, reconstruct_ev' (skipn (et_size e0) (e ++ e1)) e2 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H6.
     *)
    
    
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    rewrite H9 in *; clear H9.
    rewrite H8 in *; clear H8.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)

    assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
    {
        
        
        destruct ee; ff.
        destruct s; ff.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
    }

    invc H8.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.

    + (* t1 case *)

    assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
    {
        
        
        destruct ee; ff.
        destruct s; ff.
        ++
          rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
    }

    invc H8.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
Defined.


        
      
(*

        
    



    
      +
         destruct ee; ff.
        destruct s; ff.
        ++
          rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          3: { eassumption. }
          ff.
          2: { ff. econstructor.
            eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        ++
          rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          econstructor.
        
          
        
          eassumption.
        destruct ee.
        ff.
          econstructor. eassumption. econstructor.
          ++
            econstructor. eassumption. econstructor.
          ++
            econstructor. eassumption. econstructor.
        
      eapply IHt1 with (ecc := evc e e0).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        destruct ee.
        ff.
        inv_events.
        +
          destruct s; ff.
          ++
        
            econstructor. eassumption. econstructor.
          ++
            econstructor. eassumption. econstructor.
          ++
            econstructor. eassumption. econstructor.
        +
          destruct s; ff.
          ++
          econstructor; eassumption; econstructor.
          ++
            econstructor. eassumption. econstructor.
          ++
            econstructor. eassumption. econstructor.
          
            
      



    

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

        (*
        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
         *)
        rewrite H8 in *; clear H8.
        rewrite H9 in *; clear H9.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc := evc e e0).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.

        (*
        eassumption.
        rewrite <- Heqo.
        unfold reconstruct_ev. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor. *)
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9. *)


      (*
      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)
      
      

      invc H8.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        (*
        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor.
            ff.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor.
            ff.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
         *)
        
        rewrite H8 in *; clear H8.
        rewrite H9 in *; clear H9.






        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:=evc e e0) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
         *)
        
        rewrite H8 in *; clear H8.
        rewrite H9 in *; clear H9.




        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
*)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
         eapply IHt1 with (ecc := evc e e0).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.



        (*
        eapply IHt1 with (ecc:= evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor. *)
      }

      (*
       assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)
      ff.

      rewrite H8 in *; clear H8.
      rewrite H9 in *; clear H9.

      repeat ff.

      rewrite fold_recev in *.


      destruct s.
      ++
        ff.

        (*



        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.
*)

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.


        (*


        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor. ff.
            
            eassumption.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor. ff.
            eassumption.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.
         *)
        


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
         *)
        

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc := evc e1 e2).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.
         *)
        


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
       eapply IHt2 with (ecc := evc e1 e2).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.



    - (* abparcase *)
    (*
    do_wf_pieces. *)
    edestruct wf_bpar_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    (*

    assert (exists x, reconstruct_ev' (firstn (et_size e0) (e ++ e1)) e0 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H1. 

    assert (exists x, reconstruct_ev' (skipn (et_size e0) (e ++ e1)) e2 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H6.
     *)
    
    
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

        (*
        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
         *)
        rewrite H8 in *; clear H8.
        rewrite H9 in *; clear H9.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc := evc e e0).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.

        (*
        eassumption.
        rewrite <- Heqo.
        unfold reconstruct_ev. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor. *)
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9. *)


      (*
      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)
      
      

      invc H8.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        (*
        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor.
            ff.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor.
            ff.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
         *)
        
        rewrite H8 in *; clear H8.
        rewrite H9 in *; clear H9.






        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:=evc e e0) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
         *)
        
        rewrite H8 in *; clear H8.
        rewrite H9 in *; clear H9.




        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
*)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
         eapply IHt1 with (ecc := evc e e0).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.



        (*
        eapply IHt1 with (ecc:= evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor. *)
      }

      (*
       assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)
      ff.

      rewrite H8 in *; clear H8.
      rewrite H9 in *; clear H9.

      repeat ff.

      rewrite fold_recev in *.


      destruct s.
      ++
        ff.

        (*



        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.
*)

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.


        (*


        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor. ff.
            
            eassumption.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (e:= evc [0] mt). (* (bits:=[0]) (et:=mt). *)
            apply H4.
            econstructor. ff.
            eassumption.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.
         *)
        


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
         *)
        

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc := evc e1 e2).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.
         *)
        


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
       eapply IHt2 with (ecc := evc e1 e2).
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. eassumption. econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H8.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
Defined.



(*


  - (* abpar case *)
    edestruct wf_lseq_pieces;[eauto | idtac].
    (* do_wf_pieces. *)
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    measEventFacts.
    do_pl_immut.
    do_pl_immut.
    subst.

    invc H6.

    
    inv_events.
     + (* t1 case *)
       (*clear H0. *)

       assert (
           (exists e'', EvSub (uuc i args tpl tid n e'') (fromSome mtc (reconstruct_ev ecc))) \/
           (exists ett p' bs et',
               EvSub (hhc p' bs ett) (fromSome mtc (reconstruct_ev ecc)) /\
               EvSubT (uu i args tpl tid et') ett)
         ).
              
       {
         eapply uu_preserved.
         apply H4.
         apply H5.
         5: { eassumption. }
         4: { eassumption. }
         eassumption.
              
         rewrite <- H1.
         ff.
         eassumption.

       }
       destruct H3.
       ++

       destruct_conjs.



       assert (
        exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                     (build_app_comp_evC (fromSome mtc (reconstruct_ev ecc)))).
       {
         eapply uuc_app; eauto.
       }
       destruct_conjs.
       econstructor.
       rewrite <- H1 in *.
       eassumption.
       ++
         rewrite <- H1 in *.
         ff.
         destruct_conjs.

         eapply ahuc.
         eassumption.
         (*
         apply H9. *)
         eapply hhc_app; eauto.
         (*

         assert (EvSub (hhc H2 (checkHash H1 H2 H5) H1) (build_app_comp_evC (fromSome mtc (reconstruct_ev ecc)))).
         {
           eapply hhc_app; eauto.
         }

         eapply ahuc.
         eassumption.
         eassumption. *)
     + (* t2 case *)
       assert (appEvent_EvidenceC (umeas n p0 i args tpl tid)
                                  (build_app_comp_evC (e'))).
       {
         destruct ecc.
         destruct st_ev.
         eapply IHt2.
         eassumption.
         3: { eassumption. }

         eapply wf_ec_preserved_by_cvm.
         apply H4.
         eassumption.
         eassumption.
         eassumption.
         
         (*
         
         
         2: {
           eassumption.
         }      
         eapply cvm_refines_lts_evidence.
         apply H3.
         eassumption.
         eassumption.
         tauto. *)
         econstructor.
         Check eval_aeval.
         assert (e2 = aeval t1 p et).
         {
           rewrite <- eval_aeval.
           
           eapply cvm_refines_lts_evidence.
           eassumption.
           eassumption.
         }
         subst.
         eassumption.
         econstructor.
       }
       eassumption.
       
         (*
         
         rewrite eval_aeval.
         eassumption. 
         econstructor.
       }
       eassumption. *)







       
    - (* abseq case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bseq_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    (*

    assert (exists x, reconstruct_ev' (firstn (et_size e0) (e ++ e1)) e0 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H1. 

    assert (exists x, reconstruct_ev' (skipn (et_size e0) (e ++ e1)) e2 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H6.
     *)
    
    
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc := evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo.
        unfold reconstruct_ev. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9. *)


      (*
      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)
      
      

      invc H2.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            apply H4.
            econstructor.
            ff.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            apply H4.
            econstructor.
            ff.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.






        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:=evc e e0) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.




        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
*)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:= evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
       assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)

      destruct s.
      ++
        ff.



        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.


        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            apply H4.
            econstructor. ff.
            
            eassumption.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            apply H4.
            econstructor. ff.
            eassumption.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
         *)
        

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm.
            apply H4.
            eauto.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.










        







        
    - (* abpar case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bpar_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    (*

    assert (exists x, reconstruct_ev' (firstn (et_size e0) (e ++ e1)) e0 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H1. 

    assert (exists x, reconstruct_ev' (skipn (et_size e0) (e ++ e1)) e2 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H6.
     *)
    
    
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc := evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo.
        unfold reconstruct_ev. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9. *)


      (*
      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)
      
      

      invc H2.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor.
            ff.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor.
            ff.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.






        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:=evc e e0) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.




        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
*)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:= evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
       assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)

      destruct s.
      ++
        ff.



        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.


        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor. ff.
            eassumption.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor. ff.
            eassumption.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
         *)
        

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
Defined.   




*)


 *)



(*



        
    - (* abpar case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bpar_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H5.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
      {
        eapply IHt1.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)

      destruct s.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
      {
        eapply IHt2.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
Defined.
*)
