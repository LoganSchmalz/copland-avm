(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Defs Term_Defs Term ConcreteEvidence LTS Event_system Term_system Main Appraisal_Evidence AutoPrim.
Require Import MonadVM StructTactics Auto.
Require Import Axioms_Io Impl_vm External_Facts Helpers_VmSemantics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec Lia.


Set Nested Proofs Allowed.

(*
Lemma range_par: forall t,
    range_par t = range (unannoPar t).
Proof.
  destruct t; eauto.
Defined.

Lemma wfr_implies_wfrannt :
  forall t,
    well_formed_r t ->
    well_formed_r_annt (unannoPar t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
        invc H;
    repeat find_apply_hyp_hyp;
    repeat rewrite range_par in *;
    econstructor; eauto.
Defined.
*)

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

(*
Lemma fst_annopar: forall a a' l l',
    anno_par a l = (l', a') ->
    fst (range a) = fst (Term_Defs.range_par a').
Proof.
  intros.
  generalizeEverythingElse a.
  destruct a; intros; ff.
Defined.

Lemma snd_annopar_snd: forall a a' l l',
    anno_par a l = (l', a') ->
    Term_Defs.range_par a' = range a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros; ff.
Defined.

Lemma wfr_par_irrel: forall a2 l l' l0 l0' a0 a0',
    well_formed_r_annt a2 ->
    anno_par a2 l' = (l0', a0') ->
    anno_par a2 l = (l0, a0) ->
    well_formed_r a0 ->
    well_formed_r a0'.
Proof.
  intros.
  unfold annotated_par in *.
  generalizeEverythingElse a2.
  induction a2; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    invc H2.
    invc H.
    
    assert (well_formed_r a2).
    {
      eauto.
    }
    assert (well_formed_r a3).
    {
      eauto.
    }
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.
    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    subst'.
    congruence.

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a3).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
  -
    ff.
    invc H2.
    invc H.
    
    assert (well_formed_r a2).
    {
      eauto.
    }
    assert (well_formed_r a3).
    {
      eauto.
    }
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    subst'.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.

    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    subst'.
    congruence.

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a3).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
  -
    ff.
    invc H2.
    
    invc H.
    
    assert (well_formed_r a1).
    {
      eauto.
    }
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    subst'.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.
    subst'.
    subst'.
    rewrite <- H9.

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
    congruence.
Defined.

Lemma wfr_annt_implies_wfr_par: forall a l a0,
    well_formed_r_annt a ->
    anno_parP a0 a l ->
    well_formed_r a0.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros;
    invc H.
  -
    invc H0.
    try econstructor;
      ff.
  -
    invc H0.
    ff.
  -
    invc H0.

    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.

    simpl.
    assert (anno_parP a a1 l).
    {
      econstructor.
      jkjke.
    }
    assert (anno_parP a0 a2 l0).
    {
      econstructor.
      jkjke.
    }

    assert (well_formed_r a) by eauto.
    assert (well_formed_r a0) by eauto.
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.

    eapply fst_annopar; eauto.

    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    congruence.
    
    subst'.

    rewrite range_par.

    assert (unannoPar a0 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -

    invc H0.

    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    (*
    invc H0. *)
    simpl.

    assert (anno_parP a a1 l).
    {
      econstructor.
      jkjke.
    }
    assert (anno_parP a0 a2 l0).
    {
      econstructor.
      jkjke.
    }

    assert (well_formed_r a) by eauto.
    assert (well_formed_r a0) by eauto.
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    rewrite H7.
    
    eapply fst_annopar; eauto.

    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    congruence.

    subst'.

    rewrite range_par.

    assert (unannoPar a0 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -
    invc H0.
    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    (*
    invc H0. *)
    simpl.

    assert (anno_parP a a1 (S l)).
    {
      econstructor.
      jkjke.
    }
    (*
    assert (anno_parP a0 a2 l0).
    {
      econstructor.
      jkjke.
    }
     *)
    

    assert (well_formed_r a) by eauto.
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    rewrite H7.

    eapply fst_annopar; eauto.
    rewrite <- H8.

    erewrite snd_annopar_snd; eauto.

    eassumption.
Defined.

Lemma annopar_well_formed_r: forall t t',
    t = annotated_par (annotated t') ->
    well_formed_r t.
Proof.
  intros.
  rewrite H in *.
  eapply wfr_annt_implies_wfr_par.
  2: {
    econstructor.
    unfold annotated_par in *.
    unfold annotated in *.
    assert (anno_par (snd (anno t' 0)) 0 = (fst (anno_par (snd (anno t' 0)) 0), snd (anno_par (snd (anno t' 0)) 0))).
    {
      destruct (anno_par (snd (anno t' 0)) 0); tauto.
    }
    reflexivity.
    (*
    jkjke.
    simpl. *)

  }
  eapply anno_well_formed_r.
  assert (anno t' 0 = (fst (anno t' 0), snd (anno t' 0))).
  {
    destruct (anno t' 0); tauto.
  }
  jkjke.
Defined.
*)

Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'' i i' i'',
    (*well_formed_r t -> *)
    copland_compile t
           {| st_ev := e; st_trace := tr1; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p'; st_evid := i' |}) ->

    copland_compile t
           {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p''; st_evid := i'' |}) ->
    
    e' = e'' /\ p' = p'' /\ i' = i''.
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_evid
            (execSt (copland_compile t)
                    {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |}) = i').
  eapply trace_irrel_evid; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.
  
  subst''.
  simpl in *.
  repeat split; try congruence.
Defined.

Lemma alseq_decomp_gen : forall t1' t2' e e'' p p'' init_tr tr i i'',
    (*well_formed_r (alseq_par r t1' t2') -> *)
    copland_compile (alseq_par t1' t2') {| st_ev := e; st_trace := init_tr; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_evid := i'' |}) ->

    exists e' tr' p' i',
      copland_compile t1' {| st_ev := e; st_trace := init_tr; st_pl := p; st_evid := i |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |}) /\
        copland_compile t2' {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} =
        (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_evid := i'' |}).     
Proof.
  intros.
  (*
  do_wf_pieces. *)
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl. exists st_evid.
  split.
  reflexivity.

  eassumption.
Defined.

Ltac do_st_trace :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i |}]
     |- context[?tr]] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} )
      tauto
  end.

Ltac do_st_trace_assumps :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i |}]
     |- _] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} )
      tauto
  end.

Ltac find_rw_in_goal :=
  match goal with
  | [H': context[?x = _]
     |- context[?x]] =>
    rewrite H'; clear H'
  end.

Ltac cumul_ih :=
  match goal with
  | [H: context[(st_trace _ = _ ++ st_trace _)],
        H': copland_compileP ?t1 {| st_ev := _; st_trace := ?m ++ ?k; st_pl := _; st_evid := _ |}
                             (Some tt)
                             ?v_full,
            H'': copland_compileP ?t1 {| st_ev := _; st_trace := ?k; st_pl := _; st_evid := _ |}
                                  (Some tt)
                                  ?v_suffix
     |- _] =>
    assert_new_proof_by (st_trace v_full = m ++ st_trace v_suffix) eauto
  end.

Ltac wrap_ccp_dohi :=
  (*do_wf_pieces; *)
  rewrite <- ccp_iff_cc in *;
  dd;
  dohi;
  rewrite ccp_iff_cc in *.

Lemma st_trace_cumul' : forall t m k e p v_full v_suffix o_suffix i,
    (*well_formed_r t -> *)

    copland_compileP t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_evid := i |}
               (Some tt) v_full ->
    
    copland_compileP t
                     {| st_ev := e; st_trace := k; st_pl := p; st_evid := i |}
                     o_suffix v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  induction t; intros.
  -
    wrap_ccp.
    
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      simpl;
      df;
      repeat rewrite app_assoc;
      reflexivity.
  -
    wrap_ccp.
    repeat rewrite app_assoc.
    reflexivity.

  - (* alseq case *)
    wrap_ccp_dohi.
     
    cumul_ih.
    dd.
    repeat do_st_trace.
    repeat find_rw_in_goal.
    eauto.

  - (* abseq case *)
    wrap_ccp_dohi.
    
    repeat rewrite <- app_assoc in *.

    cumul_ih.
    dd.
    cumul_ih.
    dd.
    rewrite app_assoc.
    eauto.
    
  - (* abpar case *)
    wrap_ccp_dohi.

    repeat rewrite <- app_assoc in *.

    cumul_ih.
    dd.
    repeat rewrite app_assoc.
    eauto.
Defined.

(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e p v_full v_suffix o_suffix i,
    (*well_formed_r t -> *)

    copland_compileP t
               {| st_ev := e; st_trace := m; st_pl := p; st_evid := i |}
               (Some tt) v_full ->
    
    copland_compileP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                     o_suffix v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  intros.
  eapply st_trace_cumul'; eauto.
  repeat rewrite app_nil_r.
  eauto.
Defined.

Lemma exists_some_cc: forall t st,
    (*well_formed_r t -> *)
    exists st',
      copland_compile t st = (Some tt, st').
Proof.
  intros.
  destruct (copland_compile t st) eqn:ee.
  do_asome.
  subst.
  eauto.
Defined.

Ltac do_exists_some_cc t st :=
    assert_new_proof_by
      (exists st', copland_compile t st = (Some tt, st') )
      ltac:(eapply exists_some_cc);
    destruct_conjs.

(*
Ltac do_exists_some_cc t st :=
  match goal with
  | [H: well_formed_r t  |- _] =>
    assert_new_proof_by
      (exists st', copland_compile t st = (Some tt, st') )
      ltac:(eapply exists_some_cc; [apply H])
  end;
  destruct_conjs.
*)

Lemma suffix_prop : forall t e e' tr tr' p p' i i',
    (*well_formed_r t -> *)
    copland_compileP t
           {| st_ev := e;
              st_trace := tr;
              st_pl := p;
              st_evid := i |}
           (Some tt)
           {|
             st_ev := e';
             st_trace := tr';
             st_pl := p';
             st_evid := i' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}.

  rewrite ccp_iff_cc in *.

  repeat do_st_trace_assumps.
  repeat find_rw_in_goal.
  eexists.
  unfold st_trace at 2.
  erewrite st_trace_cumul'.
  3: {
    apply H1.
  }
  simpl.
  tauto.
  rewrite app_nil_r.
  eassumption.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': copland_compileP ?t
         {| st_ev := _; st_trace := ?tr; st_pl := _; st_evid := _ |}
         (Some tt)
         {| st_ev := _; st_trace := ?tr'; st_pl := _; st_evid := _ |}
         (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H'])
             name
  end.

Lemma alseq_decomp : forall t1' t2' e e'' p p'' tr i i'',
    (*well_formed_r (alseq_par r t1' t2') -> *)
    copland_compileP (alseq_par t1' t2')
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := e''; st_trace := tr; st_pl := p''; st_evid := i'' |} ->

    exists e' tr' p' i',
      copland_compileP t1'
                       {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                       (Some  tt)
                       {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} /\
      exists tr'',
        copland_compileP t2'
                         {| st_ev := e'; st_trace := []; st_pl := p'; st_evid := i' |}
                         (Some tt)
                         {| st_ev := e''; st_trace := tr''; st_pl := p''; st_evid := i'' |} /\
        tr = tr' ++ tr''.     
Proof.
  intros.
  wrap_ccp_dohi.
  
  eexists.
  eexists.
  eexists.
  eexists.

  split.
  +
    eassumption.
  +
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_pl := st_pl0; st_evid := st_evid0 |}.
    vmsts.

    eexists.

    wrap_ccp_dohi.

    split.
    ++
      eassumption.
    ++
      repeat do_st_trace.
      repeat find_rw_in_goal.
      eapply st_trace_cumul; 
        eassumption.
Defined.

Lemma restl : forall t e e' x tr p p' i i',
    (*well_formed_r t -> *)
    copland_compileP t
                     {| st_ev := e; st_trace := x; st_pl := p; st_evid := i|}
                     (Some tt)
                     {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_evid := i' |} ->

    copland_compileP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := e'; st_trace := tr; st_pl := p'; st_evid := i' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}.
  wrap_ccp_dohi.

  assert (st_trace = tr).
  {
    do_st_trace.
    rewrite H0; clear H0.
    assert (tr = st_trace).
    {
      assert (StVM.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_pl := st_pl; st_evid := st_evid|} =
              x ++ StVM.st_trace {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid |}).
      {
        eapply st_trace_cumul; 
        eassumption.
      }
      simpl in *.
      eapply app_inv_head; eauto.
    }
    rewrite H0; clear H0.
    simpl.
    tauto.
  }
  congruence.
Defined.

Ltac do_restl :=
  match goal with
  | [H: copland_compileP ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i |}
        (Some tt)
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'; st_evid := ?i' |}
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by
      (copland_compileP t
                        {| st_ev := e; st_trace := []; st_pl := p; st_evid := i|}
                        (Some tt)
                        {| st_ev := e'; st_trace := x; st_pl := p'; st_evid := i' |})
      ltac:(eapply restl; [apply H])
  end.

Lemma splitEv_T_l_LEFT: forall e bits bits' es e0 sp,
    et_size e = es ->
    splitEv_l (ALL,sp) (evc bits e) = (evc bits' e0) ->
    et_size e0 = es. (* (splitEv_T_l LEFT es). *)
Proof.
  intros.
  ff.
Defined.

Lemma aeval_anno: forall a i n e0,
    (aeval (snd (anno (unanno a) i)) n e0 = aeval a n e0).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
    eauto.
    simpl.
    erewrite <- IHa.
    jkjke.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    jkjke.
    jkjke.
Defined.

Lemma evc_inv: forall e,
    e = evc (get_bits e) (get_et e).
Proof.
  destruct e; eauto.
Defined.

Lemma front_app{A} :
  forall (x:A) xs ys,
    
    x :: xs ++ ys = [x] ++ xs ++ ys.
Proof.
  intros.
  tauto.
Defined.

Lemma back_app{A:Type}: forall (x y:A),
    [x; y] = [x] ++ [y].
Proof.
  intros.
  tauto.
Defined.

(*

Ltac do_t_at_zero t x :=
  let y := fresh in
  assert (exists l' t', anno_par t 0 = (l',t')) as y by
        (destruct (anno_par t 0); repeat eexists);
  destruct y;
  destruct y as [x].

Ltac do_assert_remote t e p i :=
  assert (
      copland_compile t
                      {| st_ev := e; st_trace := []; st_pl := p; st_evid := i|} =
      (Some tt,
       {| st_ev := doRemote_session (unannoPar t) p e;
                   st_trace := cvm_events (unannoPar t) p (get_et e);
                               st_pl := p;
                                        st_evid := (i + event_id_span (unannoPar t))
       |})
    ) by
    (eapply copland_compile_at).
     (*eapply wfr_annt_implies_wfr_par; 
     [eassumption | econstructor; jkjke]). *)

Ltac do_assert_unannoPar t x :=
  assert (t = unannoPar x) by
    (erewrite anno_unanno_par;
     [reflexivity | eassumption]).

Ltac do_assume_remote t e p x :=
  do_t_at_zero t x;
  do_assert_remote x e p;
  do_assert_unannoPar t x.
 *)
Lemma annopar_fst_snd: forall t l,
    anno_par t l = (fst (anno_par t l), snd (anno_par t l)).
Proof.
  intros.
  destruct (anno_par t l).
  simpl.
  tauto.
Defined.

Ltac do_t_at_zero t x :=
  let y := fresh in
  assert (exists l' t', anno_par t 0 = (l',t')) as y by
        (destruct (anno_par t 0); repeat eexists);
  destruct y;
  destruct y as [x].

Ltac do_assert_remote t e p i :=
  assert (
      copland_compile t
                      {| st_ev := e; st_trace := []; st_pl := p; st_evid := i|} =
      (Some tt,
       {| st_ev := doRemote_session (unannoPar t) p e;
                   st_trace := cvm_events (unannoPar t) p (get_et e);
                               st_pl := p; st_evid :=  (i + event_id_span (unannoPar t))
       |})
    ) by
    (eapply copland_compile_at(*;
     eapply wfr_annt_implies_wfr_par;
     [eassumption | econstructor; jkjke]*)).

Ltac do_assert_unannoPar t x :=
  assert (t = unannoPar x) by
    (erewrite anno_unanno_par;
     [reflexivity | eassumption]).

Ltac do_assume_remote t e p i x :=
  do_t_at_zero t x;
  do_assert_remote x e p i;
  do_assert_unannoPar t x.

(*
Lemma par_evidence_r: forall a p s e e2 e3 l,
    (*well_formed_r_annt a -> *)
    parallel_vm_thread l a p (splitEv_r s e) = evc e2 e3 ->
    e3 = (eval (unanno a) p (splitEv_T_r s (get_et e))).
Proof.
  intros.


  (*
  do_assume_remote a (splitEv_r s e) p XX.

  rewrite par_evidence in *.
  rewrite <- H3 in *.
  rewrite at_evidence in *.
  rewrite H0 in *.
  erewrite eval_aeval.

  rewrite aeval_anno.
  try (erewrite <- remote_Evidence_Type_Axiom).
  rewrite at_evidence in *.
  destruct s; destruct s; destruct s0;
        simpl in *;

        (*
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno; *)
        try (unfold mt_evc in * );
        (*
    try (erewrite <- remote_Evidence_Type_Axiom); *)
    (*rewrite at_evidence; *)
    try (erewrite <- evc_inv);
    jkjke.
    
  simpl in *.
  rewrite <- evc_inv.
  repeat jkjke.
  rewrite <- H3.
  
  rewrite H0.
  tauto.
  rewrite <- H0.
  jkjke.
  rewrite H3.


  
  assert (evc e2 e3 = evc (get_bits (evc e2 e3)) (get_et (evc e2 e3))).

  {
    admit.
  }
  rewrite <- H0 in H4.
  rewrite H4.
  
  Check evc_inv.
  erewrite evc_inv.
  
  Check evc_inv.
  

  
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.

  eapply cvm_

  rewrite anno_unanno.
   *)
  

  
  destruct s.
  destruct s; destruct s0;

  simpl in *;

    (*
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno;
    try (unfold mt_evc in * );
  

  
  
    try (erewrite <- remote_Evidence_Type_Axiom);
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.




  
    simpl in *;
     *)
    
    
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno;
    try (unfold mt_evc in * );
    try (erewrite <- remote_Evidence_Type_Axiom);
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.
Defined.
 *)

Lemma par_evidence_r: forall a p s e et e2 e3 l,
    parallel_vm_thread l a p (splitEv_r s (evc e et)) = evc e2 e3 ->
    e3 = (eval a p (splitEv_T_r s et)).
Proof.
  intros.

  rewrite par_evidence in *.
  destruct s.
  destruct s; destruct s0;
    simpl in *;

    (*
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno; *)
    try (unfold mt_evc in * );
    erewrite <- remote_Evidence_Type_Axiom;
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.
Defined.

Lemma cvm_refines_lts_evidence' : forall t tr tr' bits bits' et et' p p' i i',
    (*well_formed_r t -> *)
    copland_compileP t
                     (mk_st (evc bits et) tr p i)
                     (Some tt)
                     (mk_st (evc bits' et') tr' p' i') ->
    et' = (Term_Defs.eval (unannoPar t) p et).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    destruct a;
      try (
          (*try unfold get_et; *)
          dd;
          eauto).

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    (*
    destruct e. *)
    dd.

    (*
    
    erewrite eval_aeval.
    
    
    rewrite aeval_anno. *)
    erewrite <- remote_Evidence_Type_Axiom.
    jkjke.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    (*
    eassumption. *)
    eapply restl.
    eassumption.
    destruct_conjs.

    wrap_ccp.
    
    destruct x.
    (*
    destruct e. *)
    repeat jkjke'.

    (*

    
    assert (e3 = get_et (evc e2 e3)) by tauto.
    repeat jkjke'. *)
    
  - (* abseq case *)

    wrap_ccp.
    
    do_suffix blah.
    do_suffix blah'.
    
    destruct_conjs; subst.
    repeat do_restl.

    assert (e = (eval (unannoPar t1) p (splitEv_T_l s et))).
    {
      destruct s; destruct s.
      ++
        eapply IHt1;
          eassumption.
      ++
        unfold splitEv_T_l.
        assert (mt = get_et (evc [] mt)) by tauto.
        jkjke.
    }
    dd.

    assert (e0 = (eval (unannoPar t2)) p (splitEv_T_r s et)).
    {
      destruct s.
      destruct s0.
      ++
        unfold splitEv_T_r.
        eauto.
      ++
        simpl.
        eauto.
    }
    
    simpl in *; subst.
    tauto.

  - (* abpar case *)
    wrap_ccp.

    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (e = (eval (unannoPar t)) p (splitEv_T_l s et)).
    {
      destruct s; destruct s.
      ++
        eapply IHt;
          eassumption.
      ++
        unfold splitEv_T_l.
        assert (mt = get_et (evc [] mt)) by tauto.
        jkjke.
    }
    dd.

    assert (e0 = (eval t0 p (splitEv_T_r s et))).
    {
      eapply par_evidence_r; eauto.
    }

    find_rw_in_goal.
    tauto.
Defined.

Lemma cvm_refines_lts_evidence : forall t t' tr tr' bits bits' et et' p p' i i' loc,
    (*well_formed_r t -> *)
    anno_parP t t' loc ->
    copland_compileP t
                     (mk_st (evc bits et) tr p i)
                     (Some tt)
                     (mk_st (evc bits' et') tr' p' i') ->
    et' = (Term_Defs.eval t' p et).
Proof.
  intros.
  assert (t' = unannoPar t).
  {
    destruct (anno_par t' loc) eqn: hi.
    invc H.
    erewrite anno_unanno_par.
    reflexivity.
    rewrite hi.
    simpl; tauto.
  }
  rewrite H1.
  
  eapply cvm_refines_lts_evidence'.
  eassumption.
Defined.
Check encodeEvBits.
Search "encode".



Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
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

Ltac clear_skipn_firstn :=
  match goal with
  | [H: firstn _ _ = _,
        H2: skipn _ _ = _ |- _]
    => rewrite H in *; clear H;
      rewrite H2 in *; clear H2
  end.

Lemma wfec_encodeEv_etfun:
  forall e,
    wf_ec (evc (encodeEv e) (et_fun e)).
Proof.
  intros.
  induction e; intros.
  -
    dd.
    econstructor; tauto.
  -
    dd.
    econstructor; tauto.
  -
    dd.
    econstructor.
    invc IHe.
    dd.
    jkjke.
  -
    dd.
    econstructor.
    invc IHe.
    dd.
    jkjke.
  -
    dd.
    econstructor; tauto.
  -
    dd.
    invc IHe1.
    invc IHe2.
    econstructor.
    dd.
    erewrite app_length.
    jkjke.
  -
    dd.
    invc IHe1.
    invc IHe2.
    econstructor.
    dd.
    erewrite app_length.
    jkjke.
Defined.

Lemma recon_same: forall e,
    Some e = reconstruct_ev (evc (encodeEv e) (et_fun e)).
Proof.
  intros.
  induction e; intros;
    try (dd; tauto).
  -
    dd.
    rewrite <- IHe.
    tauto.
  -
    dd.
    rewrite <- IHe.
    tauto.
  -
    dd.
    assert (wf_ec (evc (encodeEv e1) (et_fun e1))).
    {
      eapply wfec_encodeEv_etfun.
      }
    assert ((firstn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e1).
    {

      eapply wfec_firstn.
      eassumption.
    }
    assert ((skipn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e2).
    {

      eapply wfec_skipn.
      eassumption.
    }
    rewrite H0; clear H0.
    rewrite H1; clear H1.
    
    
    
    rewrite <- IHe1.
    rewrite <- IHe2.
    tauto.
  -
    dd.
    assert (wf_ec (evc (encodeEv e1) (et_fun e1))).
    {
      eapply wfec_encodeEv_etfun.
    }
    assert ((firstn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e1).
    {
     eapply wfec_firstn.
     eassumption.
    }
    assert ((skipn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e2).
    {
      eapply wfec_skipn.
      eassumption.
    }
    rewrite H0; clear H0.
    rewrite H1; clear H1.
    
    
    
    rewrite <- IHe1.
    rewrite <- IHe2.
    tauto.
Defined.

Lemma inv_recon_mt: forall ls et,
    reconstruct_evP (evc ls et) mtc ->
    et = mt.
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.
  tauto.
Defined.

Ltac do_inv_recon_mt :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) mtc

     |- _] =>
    assert_new_proof_by (et = mt) ltac:(eapply inv_recon_mt; apply H)
  end;
  subst.

Lemma inv_recon_mt': forall ls e,
    reconstruct_evP (evc ls mt) e ->
    e = mtc.
Proof.
  intros.
  invc H.
  repeat ff; try solve_by_inversion.
  tauto.
Defined.

Ltac do_inv_recon_mt' :=
  match goal with
  | [H: reconstruct_evP (evc _ mt) ?e

     |- _] =>
    assert_new_proof_by (e = mtc) ltac:(eapply inv_recon_mt'; apply H)
  end;
  subst.


Lemma inv_recon_nn: forall ls et n n0,
    reconstruct_evP (evc ls et) (nnc n n0) ->
    et = nn n /\ ls = [n0].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_nn :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (nnc ?n ?nval)

     |- _] =>
    assert_new_proof_by (et = nn n /\ ls = [nval]) ltac:(eapply inv_recon_nn; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_uu: forall ls et params n2 p ec,
    reconstruct_evP (evc ls et) (uuc params p n2 ec)  ->
    (exists ls' et', et = uu params p et' /\
                ls = n2 :: ls'). (* /\
                wf_ec (evc ls' et')). *)
Proof.
  intros.
  invc H.
  repeat ff.
  destruct et; repeat ff; try solve_by_inversion.
  
  repeat eexists.
  destruct ls; ff.
Defined.

Ltac do_inv_recon_uu :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (uuc ?params ?p ?uval _)

     |- _] =>
    assert_new_proof_by (exists ls' et', et = uu params p et' /\
                        ls = uval :: ls')
                        ltac:(eapply inv_recon_uu; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_gg: forall ls et n n0 ec,
    reconstruct_evP (evc ls et) (ggc n n0 ec) ->
    (exists ls' et', et = gg n et' /\
                ls = n0 :: ls').
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.

  repeat eexists.
  destruct ls; ff.
Defined.

Ltac do_inv_recon_gg :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (ggc ?n ?n0 _)

     |- _] =>
    assert_new_proof_by (exists ls' et', et = gg n et' /\
                                    ls = n0 :: ls')
                        ltac:(eapply inv_recon_gg; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_hh: forall ls et n n0 et',
    reconstruct_evP (evc ls et) (hhc n n0 et') ->
    (et = hh n et' ) /\ ls = [n0].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_hh :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (hhc ?n ?hval ?et')

     |- _] =>
    assert_new_proof_by (et = hh n et' /\ ls = [hval])
                        ltac:(eapply inv_recon_hh; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ss: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ssc ec1 ec2) ->
    (exists et1 et2, et = ss et1 et2).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_ss :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ssc _ _)

     |- _] =>
    assert_new_proof_by (exists et1 et2, et = ss et1 et2)
                        ltac:(eapply inv_recon_ss; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_pp: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ppc ec1 ec2) ->
    (exists et1 et2, et = pp et1 et2).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_pp :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ppc _ _)

     |- _] =>
    assert_new_proof_by (exists et1 et2, et = pp et1 et2)
                        ltac:(eapply inv_recon_pp; apply H)
  end;
  destruct_conjs;
  subst.

Ltac do_inv_recon :=
  try do_inv_recon_mt;
  try do_inv_recon_mt';
  try do_inv_recon_nn;
  try do_inv_recon_uu;
  try do_inv_recon_gg;
  try do_inv_recon_hh;
  try do_inv_recon_ss;
  try do_inv_recon_pp.

Lemma recon_inv_uu: forall n2 n3 H2 H3 e params,
    reconstruct_evP
      (evc (n3 :: H2) (uu params n2 H3))
      (uuc params n2 n3 e) ->
    reconstruct_evP (evc H2 H3) e.
Proof.
  intros.
  invc H.
  repeat ff.
  econstructor.
  symmetry.
  tauto.
Defined.

Ltac do_recon_inv_uu :=
  match goal with
  | [H: reconstruct_evP
          (evc (_ :: ?H2) (uu _ _ ?H3))
          (uuc _ _ _ ?e)
     |- _] =>
    assert_new_proof_by (reconstruct_evP (evc H2 H3) e) ltac:(eapply recon_inv_uu; apply H)
  end.

Lemma recon_inv_gg: forall sig ls p et e,
    reconstruct_evP
      (evc (sig :: ls) (gg p et))
      (ggc p sig e) ->
    reconstruct_evP (evc ls et) e.
Proof.
  intros.
  invc H.
  repeat ff.
  econstructor.
  symmetry.
  tauto.
Defined.

Ltac do_recon_inv_gg :=
  match goal with
  | [H: reconstruct_evP
          (evc (_ :: ?ls) (gg _ ?et))
          (ggc _ _ ?e)
     |- _] =>
    assert_new_proof_by (reconstruct_evP (evc ls et) e) ltac:(eapply recon_inv_gg; apply H)
  end.

Lemma recon_inv_ss: forall ls H1 H2 ec1 ec2,
    reconstruct_evP (evc ls (ss H1 H2)) (ssc ec1 ec2) ->
    reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
    reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2.
Proof.
  intros.
  invc H.
  repeat ff.
  split;
    econstructor;
    try 
      symmetry; eassumption.
Defined.

Lemma recon_inv_pp: forall ls H1 H2 ec1 ec2,
    reconstruct_evP (evc ls (pp H1 H2)) (ppc ec1 ec2) ->
    reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
    reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2.
Proof.
  intros.
  invc H.
  repeat ff.
  split;
    econstructor;
    try 
      symmetry; eassumption.
Defined.

Ltac do_recon_inv_ss :=
  match goal with
  | [H: reconstruct_evP
          (evc ?ls (ss ?H1 ?H2))
          (ssc ?ec1 ?ec2)
     |- _] =>
    assert_new_proof_by
      (reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
       reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2)
      ltac:(eapply recon_inv_ss; apply H)
  end; destruct_conjs.

Ltac do_recon_inv_pp :=
  match goal with
  | [H: reconstruct_evP
          (evc ?ls (pp ?H1 ?H2))
          (ppc ?ec1 ?ec2)
     |- _] =>
    assert_new_proof_by
      (reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
       reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2)
      ltac:(eapply recon_inv_pp; apply H)
  end; destruct_conjs.

Ltac do_recon_inv :=
  try do_recon_inv_uu;
  try do_recon_inv_gg;
  try do_recon_inv_ss;
  try do_recon_inv_pp.

Lemma etfun_reconstruct: forall e e0 e1,
    reconstruct_evP (evc e0 e1) e ->
    e1 = et_fun e.
Proof.
  intros.
  generalizeEverythingElse e1.
  induction e1; intros e e0 H;
    do_inv_recon;
    ff;
    invc H;
    repeat ff;
    rewrite fold_recev in *;
    do_wrap_reconP;
    repeat jkjke.
Defined.

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

Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p' i i',
    (*well_formed_r t1 -> *)
    wf_ec e ->
        copland_compileP t1
                    {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |}
                    (Some tt)
                    {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  -
    rewrite <- ccp_iff_cc in *.
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      ff;
      inv_wfec;
      try (
          econstructor;
          ff;
          try tauto;
          try congruence).  
  -
    wrap_ccp.

    eapply wf_ec_preserved_remote; eauto.

  -
    wrap_ccp.
    eauto.
  -
    wrap_ccp.

    do_wfec_split.

    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    econstructor.
    dd.
    inv_wfec.
    repeat jkjke'.
    eapply app_length.

  -
    wrap_ccp.
    
    do_wfec_split.

    find_apply_hyp_hyp.

      inv_wfec;
      ff;
      econstructor;
      dd;
      repeat jkjke'.

    erewrite app_length.

    assert (wf_ec (evc r0 e1)).
    {
      rewrite par_evidence in Heqe1.
      rewrite <- at_evidence in Heqe1.
      rewrite <- Heqe1.
      eapply wf_ec_preserved_remote.
      econstructor.
      eassumption.
    }

    solve_by_inversion.
Defined.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [(*H: well_formed_r ?t, *)
          H2: wf_ec ?stev,
              H3: copland_compileP ?t
                                   {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |}
                                   (Some tt)
                                   {| st_ev := ?stev'; st_trace := _; st_pl := _; st_evid := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [(*apply H |*) apply H2 | apply H3])
                                 
    end.

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
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
      ltac:(eapply H with (r:=e'); (* TODO:  make r less one-off *)
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.

Locate peel_fact.

Lemma some_recons : forall e,
    wf_ec e ->
    exists ee, Some ee = reconstruct_ev e.
Proof.
  intros.
  destruct e.
  generalizeEverythingElse e.
  induction e; intros.
  -






  try (ff; eauto; tauto).
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
    eauto.
  -
      try (ff; eauto; tauto).
    try
      ( inv_wfec; ff;
        do_some_recons').
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke').



    inv_wfec; ff;
      repeat do_rcih;
      destruct_conjs.
    repeat jkjke'.
    repeat jkjke'.
    find_inversion.
    do_rcih.
    eauto.
     assert (r = []).
     { destruct r; try solve_by_inversion. }
     subst.
     solve_by_inversion.
  -
    try (ff; eauto; tauto).
    try
      ( inv_wfec; ff;
        do_some_recons').
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke').
        inv_wfec; ff;
      repeat do_rcih;
      destruct_conjs.
    repeat jkjke'.
    repeat jkjke'.
    find_inversion.
    do_rcih.
    eauto.
     assert (r = []).
     { destruct r; try solve_by_inversion. }
     subst.
     solve_by_inversion.
  -
        try (ff; eauto; tauto).
    try
      ( inv_wfec; ff;
        do_some_recons').
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke').
        inv_wfec; ff;
      repeat do_rcih;
      destruct_conjs.
    repeat jkjke'.
    repeat jkjke'.
    find_inversion.

    destruct r; try solve_by_inversion.
    dd.
    destruct r; try solve_by_inversion.
  -
            try (ff; eauto; tauto).
    try
      ( inv_wfec; ff;
        do_some_recons').
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke').
        inv_wfec; ff;
      repeat do_rcih;
      destruct_conjs.
    repeat jkjke'.
    repeat jkjke'.
    find_inversion.

    destruct r; try solve_by_inversion.
    dd.
    destruct r; try solve_by_inversion.
  -
            try (ff; eauto; tauto).
    try
      ( inv_wfec; ff;
        do_some_recons').
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke').
        inv_wfec; ff;
      repeat do_rcih;
      destruct_conjs.
        eauto.


        edestruct IHe2 with (r:=  (skipn (et_size e1) r)).
        econstructor.
        eapply skipn_long.
        eassumption.
        rewrite <- H in *.
        solve_by_inversion.

        edestruct IHe1 with (r:=  (firstn (et_size e1) r)).
        econstructor.
        eapply firstn_long.
        lia.
        rewrite <- H in *.
        solve_by_inversion.
  -
                try (ff; eauto; tauto).
    try
      ( inv_wfec; ff;
        do_some_recons').
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke').
        inv_wfec; ff;
      repeat do_rcih;
      destruct_conjs.
        eauto.


        edestruct IHe2 with (r:=  (skipn (et_size e1) r)).
        econstructor.
        eapply skipn_long.
        eassumption.
        rewrite <- H in *.
        solve_by_inversion.

        edestruct IHe1 with (r:=  (firstn (et_size e1) r)).
        econstructor.
        eapply firstn_long.
        lia.
        rewrite <- H in *.
        solve_by_inversion.
Defined.

Lemma some_reconsP : forall e,
    wf_ec e ->
    exists ee, reconstruct_evP e ee.
Proof.
  intros.
  edestruct some_recons.
  eassumption.
  eexists.
  econstructor.
  eassumption.
Defined.

Ltac do_somerecons :=
  repeat
    match goal with
    | [H: wf_ec ?e
       |- _ ] =>
      assert_new_proof_by
        (exists x, reconstruct_evP e x)
        ltac:(eapply some_reconsP; apply H)     
    end; destruct_conjs.

Definition cvm_evidence_denote_asp (a:ASP) (p:Plc) (e:EvidenceC) (x:Event_ID): EvidenceC :=
  match a with
  | CPY => e
  | ASPC params => uuc params p (do_asp params p x) e
  | SIG => ggc p (do_sig (encodeEvRaw (encodeEv e)) p x) e 
  | HSH => hhc p (do_hash (encodeEvRaw (encodeEv e)) p) (et_fun e)
  end.

Fixpoint cvm_evidence_denote (t:AnnoTerm) (p:Plc) (ec:EvidenceC) : EvidenceC :=
  match t with
  | aasp (i,_) x => cvm_evidence_denote_asp x p ec i
  | aatt _ q x => cvm_evidence_denote x q ec
  | alseq _ t1 t2 => cvm_evidence_denote t2 p (cvm_evidence_denote t1 p ec)
  | abseq _ s t1 t2 => ssc (cvm_evidence_denote t1 p ((splitEvl s ec)))
                         (cvm_evidence_denote t2 p ((splitEvr s ec)))
  | abpar _ s t1 t2 => ppc (cvm_evidence_denote t1 p ((splitEvl s ec)))
                         (cvm_evidence_denote t2 p ((splitEvr s ec)))
  end.

Lemma recon_encodeEv: forall bits et ec,
    reconstruct_evP (evc bits et) ec ->
    encodeEv ec = bits.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    dd.
    do_inv_recon.
    invc H.
    ff.
  -
    dd.
    do_inv_recon.
    ff.
  -
    do_inv_recon.
    ff.
    invc H.
    ff.
    assert (reconstruct_evP (evc H0 H1) e).
    {
      econstructor; eauto.
    }
    assert (encodeEv e = H0) by eauto.
    congruence.
  -
    do_inv_recon.
    ff.
    invc H.
    ff.
    rewrite fold_recev in *.
    do_wrap_reconP.
    (*
      assert (reconstruct_evP (evc H0 H1) e).
      {
        econstructor; eauto.
      } *)
    assert (encodeEv e = H0) by eauto.
    congruence.
  -
    do_inv_recon.
    ff.
  -
    do_inv_recon.
    ff.
    invc H.
    ff.
    rewrite fold_recev in *.
    do_wrap_reconP.
    
    
    assert (encodeEv e =  (firstn (et_size H0) bits)) by eauto.
    assert (encodeEv e0 = (skipn (et_size H0) bits)) by eauto.

    assert (bits = firstn (et_size H0) bits ++ skipn (et_size H0) bits).
    {
      symmetry.
      eapply firstn_skipn.
    }
    rewrite H3 at 1.
    congruence.
  -
    do_inv_recon.
    ff.
    invc H.
    ff.
    rewrite fold_recev in *.
    do_wrap_reconP.
    
    
    assert (encodeEv e =  (firstn (et_size H0) bits)) by eauto.
    assert (encodeEv e0 = (skipn (et_size H0) bits)) by eauto.

    assert (bits = firstn (et_size H0) bits ++ skipn (et_size H0) bits).
    {
      symmetry.
      eapply firstn_skipn.
    }
    rewrite H3 at 1.
    congruence.
Defined.

Lemma recon_encodeEv_Raw: forall ec bits et,
    reconstruct_evP (evc bits et) ec ->
    encodeEvRaw (encodeEv ec) = encodeEvBits (evc bits et).
Proof.
  intros.
  unfold encodeEvBits.
  erewrite recon_encodeEv.
  tauto.
  eauto.
Defined.


(*
Lemma encodeEvBits_iff_Raw: forall e,
    encodeEvBits (evc (encodeEv e) (et_fun e)) = encodeEvRaw (encodeEv e).
Proof.
  intros.
  assert (reconstruct_evP (evc (encodeEv e) (et_fun e)) e).
  {
    econstructor.
    eapply recon_same.
  }
  erewrite recon_encodeEv_Raw.
  reflexivity.
  eassumption.
Defined.
*)

(*
Lemma reconp_wfec: forall ecc e,
    reconstruct_evP ecc e ->
    wf_ec ecc.
Proof.
  intros.
Admitted.
*)

Lemma wfec_recon: forall ee ec,
    reconstruct_evP ee ec ->
    wf_ec ee.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros; destruct ee.
  -
    do_inv_recon.
    dd.
    invc H.
    dd.
    ff.
    econstructor. tauto.
  -
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
  -
    do_inv_recon.
    invc H.
    dd.
    ff.
    assert (wf_ec (evc H0 H1)).
    {
      apply IHec.
      econstructor.
      eauto.
    }
    econstructor.
    dd.
    invc H.
    lia.
  -
    do_inv_recon.
    invc H.
    dd.
    ff.
    assert (wf_ec (evc H0 H1)).
    {
      apply IHec.
      econstructor.
      eauto.
    }
    econstructor.
    dd.
    invc H.
    lia.
  -
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
  -
    do_inv_recon.
    invc H.
    dd.
    ff.

    assert (wf_ec (evc (firstn (et_size H0) r) H0)).
    {
      apply IHec1.
      econstructor.
      eauto.
    }
    assert (wf_ec (evc (skipn (et_size H0) r) H1)).
    {
      apply IHec2.
      econstructor.
      eauto.
    }
    
    econstructor.
    dd.
    invc H.
    invc H2.
    rewrite <- H4.
    rewrite <- H3.
    Check firstn_skipn.
    assert (r = firstn (et_size H0) r ++ skipn (et_size H0) r).
    {
      symmetry.
      eapply firstn_skipn.
    }
    rewrite H at 1.
    eapply app_length.
  -
        do_inv_recon.
    invc H.
    dd.
    ff.

    assert (wf_ec (evc (firstn (et_size H0) r) H0)).
    {
      apply IHec1.
      econstructor.
      eauto.
    }
    assert (wf_ec (evc (skipn (et_size H0) r) H1)).
    {
      apply IHec2.
      econstructor.
      eauto.
    }
    
    econstructor.
    dd.
    invc H.
    invc H2.
    rewrite <- H4.
    rewrite <- H3.
    Check firstn_skipn.
    assert (r = firstn (et_size H0) r ++ skipn (et_size H0) r).
    {
      symmetry.
      eapply firstn_skipn.
    }
    rewrite H at 1.
    eapply app_length.
Defined.

Lemma eval_aeval': forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    erewrite IHt1_1.
    eauto.
  -
    ff.
    erewrite IHt1_1.
    erewrite IHt1_2.
    eauto.
  -
    ff.
    erewrite IHt1_1.
    erewrite IHt1_2.
    eauto. 
Defined.

Lemma cvm_spans': forall t e tr p i e' tr' p' i',
    copland_compileP t
                     {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_pl := p';
                       st_evid := i'
                     |} ->
    i' = i + event_id_span (unannoPar t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    +
      wrap_ccp.
      tauto.
    +
      wrap_ccp.
      unfold tag_ASP in *.
      destruct a.
      ff.
    +
      wrap_ccp.
      tauto.
    +
      wrap_ccp.
      tauto.
  -
    wrap_ccp.
    simpl.
    lia.
  -
    wrap_ccp.
    assert (st_evid0 = i + event_id_span (unannoPar t1)) by eauto.
    assert (i' = st_evid0 + event_id_span (unannoPar t2)) by eauto.
    subst.
    lia.
  -
    wrap_ccp.
    assert (st_evid1 = (i + 1) + event_id_span (unannoPar t1)) by eauto.
    assert (st_evid = st_evid1 + event_id_span (unannoPar t2)) by eauto.
    subst.
    lia.
  -
    wrap_ccp.
    assert (st_evid = (i + 1) + event_id_span (unannoPar t)) by eauto.
    subst.
    lia.
Defined.

Lemma cvm_spans: forall t t' e tr p i e' tr' p' i' loc,
    anno_parP t t' loc ->
    copland_compileP t
                     {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_pl := p';
                       st_evid := i'
                     |} ->
    i' = i + event_id_span t'.
Proof.
  intros.
  assert (t' = unannoPar t).
  {
    destruct (anno_par t' loc) eqn: hi.
    invc H.
    erewrite anno_unanno_par.
    reflexivity.
    jkjke.
  }
  rewrite H1.
  eapply cvm_spans'; eauto.
Defined.
  

Lemma span_cvm: forall atp t annt loc i j e e' tr tr' p p' i',
    copland_compileP atp
                     {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} 
                     (Some tt)
                     {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
    
    anno_parP atp t loc ->
    anno t i = (j, annt) ->
    j = i'.

Proof.
  intros.
  assert (j = i + event_id_span t).
  {
    assert (j - i = event_id_span t).
    {
      symmetry.
      eapply span_range.
      eauto.
    }
    rewrite <- H2.
    assert (j > i).
    {
      eapply anno_mono; eauto.
    }
    
    lia.
  }
  subst.
  symmetry.
  eapply cvm_spans; eauto.
Defined.

Lemma cvm_raw_evidence_denote_fact : forall t annt t' tr tr' bits bits' et et' p p' i i' loc ec ec',
    (*well_formed_r t -> *)
    anno_parP t t' loc ->
    annoP annt t' i ->
    copland_compileP t
                     (mk_st (evc bits et) tr p i)
                     (Some tt)
                     (mk_st (evc bits' et') tr' p' i') ->
    reconstruct_evP (evc bits et) ec ->
    reconstruct_evP (evc bits' et') ec' ->

    cvm_evidence_denote annt p ec = ec'.
   (* et' = (Term_Defs.eval t' p et). *)
Proof.
  intros.
  generalizeEverythingElse t'.
  induction t'; intros.
  -
    invc H0.
    invc H.
    dd.
    destruct a.
    +
      wrap_ccp.
      Search "determ".
      eapply reconP_determ; eauto.
    +
      wrap_ccp.
      unfold tag_ASP in *.
      dd.
      invc H3.
      invc H2.
      dd.
      jkjke'.
      dd.
      tauto.
    +
      wrap_ccp.
      invc H3; invc H2.
      dd.
      jkjke'.
      dd.
      assert (encodeEvRaw (encodeEv ec) = (encodeEvBits (evc bits et))).
      {


        eapply recon_encodeEv_Raw.
        econstructor.
        eauto.
      }
      unfold encodeEvBits in *.
      congruence.
    +
      wrap_ccp.
      invc H3; invc H2.
      dd.
      assert (et_fun ec = et).
      {
        Check etfun_reconstruct.
        symmetry.
        eapply etfun_reconstruct.
        econstructor.
        eassumption.
      }
      
      erewrite recon_encodeEv_Raw.
      rewrite H.
      tauto.
      econstructor.
      eassumption.
  -
    wrap_ccp.
    invc H; invc H0.
    dd.
    do_anno_redo.

    do_assume_remote t' (evc bits et) p (S i) HHH.
    rewrite <- H1 in *; clear H1.
    rewrite H5 in *.
    simpl in *.

    eapply IHt'.
    econstructor.
    reflexivity.
    eassumption.
    rewrite H.
    dd.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
  -
    
    wrap_ccp.
    inversion H0.
    dd.
    assert (n0 = st_evid0).
    {
      Search "span".
      assert (event_id_span t'1 = n0 - i).
      {
        eapply span_range; eauto.
      }
      assert (st_evid0 = i + event_id_span t'1).
      {
        eapply cvm_spans; eauto.
      }
      assert (n0 > i).
      {
        eapply anno_mono; eauto.
      }
      lia.
    }

    dd.
    assert (n1 = i').
    {
      assert (event_id_span t'2 = n1 - st_evid0).
      {
        eapply span_range; eauto.
      }
      assert (i' = st_evid0 + event_id_span t'2).
      {
        eapply cvm_spans; eauto.
      }
      assert (n1 > st_evid0).
      {
        eapply anno_mono; eauto.
      }
      lia.
    }
    subst.

    dd.
    repeat do_anno_redo.



    destruct st_ev0.



    assert (wf_ec (evc bits et)).
    {
      eapply wfec_recon; eauto.
    }

    do_wfec_preserved.

    do_somerecons.

    (*

    do_somerecons.
    do_somerecons.
    do_somerecons.
    Print do_somerecons.
    

    Print do_somerecons.

    do_somerecons.

    assert (wf_ec (evc r e)).
    {
      Search "preserved".
      eapply wf_ec_preserved_by_cvm.
      

    Print do_wfec_preserved.

    do_wfec_preserved.

    Search "preserved".
    

    do_wfec_preserved.
     *)
    


    assert ((cvm_evidence_denote a1 p ec) = H7).
    {
      eapply IHt'1.
    
    apply Heqp0.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    }
    (*
    assert (st_evid0 = n).
    {
      Check cvm_spans.
      assert (st_evid0 = i + event_id_span t'1).
      {
        eapply cvm_spans.
        eassumption.
        eassumption.
      }
      rewrite H12.
      inversion Heqp4.
      assert (n = i + 
      Check span_range.
      
      assert (event_id_span t'1 = 

      
      Locate span_range.
      
      admit.
    }
     *)
    
    subst.
    
    
    eapply IHt'2.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
  -
    wrap_ccp.
    invc H0.
    dd.
    assert (n = st_evid1).
    {
      assert (event_id_span t'1 = n - (S i)).
      {
        eapply span_range; eauto.
      }
      assert (st_evid1 = (i + 1) + event_id_span t'1).
      {
        eapply cvm_spans; eauto.
      }
      assert (n > (S i)).
      {
        eapply anno_mono; eauto.
      }
      lia.
    }
    dd.
    assert (n0 = st_evid).
    {
      assert (event_id_span t'2 = n0 - st_evid1).
      {
        eapply span_range; eauto.
      }
      assert (st_evid = st_evid1 + event_id_span t'2).
      {
        eapply cvm_spans; eauto.
      }
      assert (n0 > st_evid1).
      {
        eapply anno_mono; eauto.
      }
      lia.
    }
    repeat do_anno_redo.

    assert (wf_ec (evc bits et)).
    {
      eapply wfec_recon; eauto.
    }

    do_wfec_split.

    do_wfec_preserved.
    do_rewrap_reconP.
    
    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    assert ((cvm_evidence_denote a1 p (splitEvl s ec)) = e1).
    {
      assert (i + 1 = S i) by lia.
      rewrite H0 in *; clear H0.
      destruct s; destruct s; destruct s0; dd.
      +
        eauto.
      +
        eauto.    
      +
        eapply IHt'1.
        eassumption.
        eassumption.
        eassumption.
        econstructor. tauto.
        eassumption.
        
      + eapply IHt'1.
        eassumption.
        eassumption.
        eassumption.
        econstructor. tauto.
        eassumption.
    }
    jkjke.

    assert ((cvm_evidence_denote a2 p (splitEvr s ec)) = e2).
    {
      (*
      assert (n = st_evid1).
      {
        admit.
      }
       *)
      
      subst.
      
      assert (i + 1 = S i) by lia.
      rewrite H0 in *; clear H0.
      destruct s; destruct s; destruct s0; dd.
      +
        eauto.
      +
        eapply IHt'2.
        eassumption.
        eassumption.
        eassumption.
        econstructor. tauto.
        eassumption.
      +
        eauto.
      +
        eapply IHt'2.
        eassumption.
        eassumption.
        eassumption.
        econstructor. tauto.
        eassumption.
    }
    congruence.
  - (* abpar case *)
    wrap_ccp.
    invc H0.
    dd.
    assert (n = st_evid).
    {
      assert (event_id_span t'1 = n - (S i)).
      {
        eapply span_range; eauto.
      }
      assert (st_evid = (i + 1) + event_id_span t'1).
      {
        eapply cvm_spans; eauto.
      }
      assert (n > (S i)).
      {
        eapply anno_mono; eauto.
      }
      lia.
    }
    dd.

    repeat do_anno_redo.

    assert (wf_ec (evc bits et)).
    {
      eapply wfec_recon; eauto.
    }

    do_wfec_split.

    do_wfec_preserved.
    do_rewrap_reconP.
    
    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    do_assume_remote t'2 (splitEv_r s (evc bits et)) p st_evid HHH.

    

    assert ((cvm_evidence_denote a0 p (splitEvl s ec)) = e1).
    {
      assert (i + 1 = S i) by lia.
      rewrite H8 in *; clear H8.
      destruct s; destruct s; destruct s0; dd.
      +
        eauto.
      +
        eauto.    
      +
        eapply IHt'1.
        eassumption.
        eassumption.
        eassumption.
        econstructor. tauto.
        eassumption.
        
      + eapply IHt'1.
        eassumption.
        eassumption.
        eassumption.
        econstructor. tauto.
        eassumption.
    }
    jkjke.

    assert ((cvm_evidence_denote a1 p (splitEvr s ec)) = e2).
    {
      (*
      assert (n = st_evid).
      {
        admit.
      }
      rewrite H9 in *; clear H9. *)
      rewrite at_evidence in *.
      rewrite par_evidence in *.
      rewrite H7 in *.
      rewrite Heqe0 in *.
      
      
      destruct s; destruct s; destruct s0; simpl.
      +
      eapply IHt'2.
      econstructor.
      reflexivity.
      eassumption.
      rewrite H7.
      erewrite anno_unanno_par.
      rewrite H3.
      simpl.
      econstructor.
      simpl in *.
      eassumption.
      rewrite H3. tauto.
      eassumption.
      eassumption.
      +
        eapply IHt'2.
      econstructor.
      reflexivity.
      eassumption.
      rewrite H7.
      erewrite anno_unanno_par.
      rewrite H3.
      simpl.
      econstructor.
      simpl in *.
      eassumption.
      rewrite H3. tauto.
      econstructor; tauto.
      eassumption.
      +
      eapply IHt'2.
      econstructor.
      reflexivity.
      eassumption.
      rewrite H7.
      erewrite anno_unanno_par.
      rewrite H3.
      simpl.
      econstructor.
      simpl in *.
      eassumption.
      rewrite H3. tauto.
      eassumption.
      eassumption.
      +
      eapply IHt'2.
      econstructor.
      reflexivity.
      eassumption.
      rewrite H7.
      erewrite anno_unanno_par.
      rewrite H3.
      simpl.
      econstructor.
      simpl in *.
      eassumption.
      rewrite H3. tauto.
      econstructor; tauto.
      eassumption.
    }
    congruence.
Defined.

Lemma cvm_ev_denote_evtype: forall annt t i p e,
    annoP annt t i ->
    et_fun (cvm_evidence_denote annt p e) = (aeval annt p (et_fun e)).
Proof.
  Check cvm_refines_lts_evidence.
  intros.

  
  inversion H.
  rewrite H0 at 2.
  destruct (anno_par t i) eqn: hi.
  simpl.
  destruct (copland_compile a
                            {|
                              st_ev := evc (encodeEv e) (et_fun e);
                              st_trace := [];
                              st_pl := p;
                              st_evid := i
                            |}) eqn: hey.
  assert (o = Some tt).
  {
    Search "some".
    eapply always_some.
    eassumption.
  }
  rewrite H4 in *; clear H4.
  vmsts.
  destruct st_ev.
  assert (wf_ec (evc (encodeEv e) (et_fun e))).
  {
    eapply wfec_encodeEv_etfun.
  }
  assert (wf_ec (evc r e0)).
  {
    eapply wf_ec_preserved_by_cvm.
    eassumption.
    econstructor.
    eassumption.
  }
  assert (reconstruct_evP (evc (encodeEv e) (et_fun e)) e).
  {
    econstructor.
    eapply recon_same.
  }
  assert (exists ecc, reconstruct_evP (evc r e0) ecc).
  {
    assert (exists ecc, Some ecc = reconstruct_ev (evc r e0)).
    {
      eapply some_recons; eauto.
    }
    destruct_conjs.
    exists H7.
    econstructor.
    eassumption.
  }
  destruct_conjs.
  
  
  assert (cvm_evidence_denote annt p e = H7).
  {
    rewrite <- H3 in *; clear H3.
    rewrite <- H2 in *; clear H2.
    eapply cvm_raw_evidence_denote_fact.
    econstructor.
    reflexivity.
    econstructor.
    jkjke.
    rewrite hi.
    simpl.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
  }

  (*
  
    jkjke.
    simpl.
    subst.
    eassumption.
   *)
  
  

  (*
  assert (e0 = (et_fun (cvm_evidence_denote annt p e))).
  assert (exists bits', st_ev = (evc bits' (et_fun (cvm_evidence_denote annt p e)))).
  {
    eexists.
    
    admit.
  }
  destruct_conjs.
  rewrite H5 in *; clear H5.
    
  (*
  assert (st_ev = aeval annt p (et_fun e)).
   *)
   *)
  rewrite H9.

  assert (e0 = et_fun H7).
  {
    eapply etfun_reconstruct.
    eauto.
  }
  rewrite <- H10.
  
    



  
  Check eval_aeval.
  Locate eval_aeval.
  erewrite <- eval_aeval.
  eapply cvm_refines_lts_evidence.
  econstructor.
  reflexivity.
  rewrite hi.
  simpl.
  econstructor.
  eassumption.
Defined.




(*
Lemma cvm_refines_lts_evidence' : forall t tr tr' e e' p p',
    well_formed_r t ->
    copland_compileP t
                     (mk_st e tr p)
                     (Some tt)
                     (mk_st e' tr' p') ->
    get_et e' = (Term_Defs.eval (unanno (unannoPar t)) p (get_et e)).

Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    destruct a;
      try (
          try unfold get_et;
          dd;
          eauto).

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    destruct e.
    dd.
    
    erewrite eval_aeval.
    
    rewrite aeval_anno.
    eapply remote_Evidence_Type_Axiom.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.
    destruct_conjs.

    wrap_ccp.
    
    destruct x.
    destruct e.

    
    assert (e3 = get_et (evc e2 e3)) by tauto.
    repeat jkjke'.
    
  - (* abseq case *)

    wrap_ccp.
    
    do_suffix blah.
    do_suffix blah'.
    
    destruct_conjs; subst.
    repeat do_restl.

    assert (e1 = get_et (evc e0 e1)) by tauto.
    jkjke.
    assert (e3 = get_et (evc e2 e3)) by tauto.
    jkjke.

    assert (get_et (evc e0 e1) = (eval (unanno (unannoPar t1)) p (splitEv_T_l s (get_et e)))).
    {
      destruct s; destruct s.
      ++
        eapply IHt1;
          eassumption.
      ++
        unfold splitEv_T_l.
        assert (mt = get_et (evc [] mt)) by tauto.
        jkjke.
    }
    dd.
    
    assert (get_et (evc e2 e3) = (eval (unanno (unannoPar t2)) p (splitEv_T_r s (get_et e)))).
    {
      destruct s.
      destruct s0.
      ++
        unfold splitEv_T_r.
        eauto.
      ++
        assert (mt = get_et (evc [] mt)) by tauto.
        jkjke.
        eauto.
    }
    simpl in *; subst.
    tauto.

  - (* abpar case *)
    wrap_ccp.

    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (e1 = get_et (evc e0 e1)) by tauto.
    jkjke.
    assert (e3 = get_et (evc e2 e3)) by tauto.
    jkjke.

    assert (get_et (evc e0 e1) = (eval (unanno (unannoPar t)) p (splitEv_T_l s (get_et e)))).
    {
      destruct s; destruct s.
      ++
        eapply IHt;
          eassumption.
      ++
        unfold splitEv_T_l.
        assert (mt = get_et (evc [] mt)) by tauto.
        jkjke.
    }
    dd.

    assert (e3 = (eval (unanno a) p (splitEv_T_r s (get_et e)))).
    {
      eapply par_evidence_r; eauto.
    }

    find_rw_in_goal.
    tauto.
    Unshelve.
    eauto.
Defined.

Lemma cvm_refines_lts_evidence : forall t tr tr' bits bits' et et' p p',
    well_formed_r t ->
    copland_compileP t
                     (mk_st (evc bits et) tr p)
                     (Some tt)
                     (mk_st (evc bits' et') tr' p') ->
    et' = (Term_Defs.eval (unanno (unannoPar t)) p et).
Proof.
  intros.
  assert (et = get_et (evc bits et)) by tauto.
  assert (et' = get_et (evc bits' et')) by tauto.
  rewrite H1; rewrite H2.
  eapply cvm_refines_lts_evidence'; eauto.
Defined.
*)

Check eval_aeval.


Lemma cvm_refines_lts_event_ordering : forall t atp annt cvm_tr bits bits' et et' p p' i i' loc,
    anno_parP atp t loc ->
    annoP annt t i ->
    (*
    well_formed_r_annt annt -> *)
    copland_compileP atp
                     (mk_st (evc bits et) [] p i)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr p' i') ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros t atp annt cvm_tr bits bits' et et' p p' i i' loc annoParPH annPH H'.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    wrap_ccp.
    invc annPH;
      destruct a; df;   
        repeat break_match; try solve_by_inversion;
          try unfold tag_ASP in *;
          df;
          
          econstructor; try (econstructor; reflexivity).
    
  - (* aatt case *)
    wrap_ccp.

    (*
    rewrite <- ccp_iff_cc in *.
    destruct r. 
     *)
    
    repeat (df; try dohtac; df).

    inv_annoparP.
    invc annPH.
    cbn in *.
    repeat break_let.
    assert (annoP a t (S i)).
    {
      econstructor.
      jkjke.
    }
    dd.

    assert (t = unanno a) as H3.
    {
      invc H1.
      rewrite anno_unanno.
      tauto.
    }
    
    assert (lstar (conf a p et) (cvm_events t p et) (stop p (aeval a p et))).
    {
      rewrite H3.

      apply remote_LTS.
    }

    
    assert (i = fst (i, S n)) as H2 by tauto.
    

    rewrite H2 at 2.
    rewrite H3.


                                
    
    eapply lstar_tran.
    econstructor.
    (*econstructor. *)
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    rewrite <- H3.
    cbn.
    eassumption.

    
    jkjke.
    simpl.
    assert (et' = (aeval a p et)).
    {
      rewrite <- eval_aeval'.
      erewrite <- remote_Evidence_Type_Axiom.
      rewrite <- H3.
      rewrite H0.
      tauto.
    }
    rewrite <- H4.
    rewrite <- H3.

    assert ((S i) + event_id_span t = n).
    {
      assert (event_id_span t = n - (S i)).
      {
        eapply span_range.
        eassumption.
      }
      rewrite H5.
      assert (n > (S i)).
      {
        eapply anno_mono.
        eassumption.
      }
      lia.
    }

    assert ((i + 1 + event_id_span t) = (S i) + event_id_span t).
    {
      lia.
    }
    rewrite H6.
    rewrite H5.
    rewrite H0.
    simpl.
    
    

    
    econstructor.

    apply stattstop.
    econstructor.

  -  (* alseq case *)
    (*
    do_wf_pieces. *)

    invc annoParPH.
    invc annPH.
    dd.
    do_annopar_redo.
    do_annopar_redo.

    
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    destruct x.

    
 
    econstructor.
    econstructor.
    subst.
    eapply lstar_transitive.
    eapply lstar_stls.
    
    eapply IHt1.
    eassumption.
    econstructor; jkjke.
    eassumption.

    eapply lstar_silent_tran.
    apply stlseqstop.

    eapply IHt2. (*with (e:= x). *)
    eassumption.
    econstructor; jkjke.
    assert (e = Term_Defs.eval t1 p et).
    eapply cvm_refines_lts_evidence.
    eassumption.
    eassumption.


    subst.
    rewrite <- eval_aeval'.
    assert (unannoPar a = unanno a1).
    {
      assert (unannoPar a = t1).
      {
        inversion Heqp0.
        destruct (anno_par t1 loc) eqn: hi.
        eapply anno_unanno_par.
        rewrite H5.
        simpl.
        eassumption.
      }
      assert (unanno a1 = t1).
      {
        
        erewrite <- anno_unanno.
        rewrite Heqp2.
        simpl.
        tauto.
      }
      congruence.
    }
    rewrite <- H5.
    assert (H0 = p).
    { wrap_ccp.
      tauto.
    }
    subst.
    assert (H1 = i + event_id_span t1).
    {

      (*
      assert (t1 = unannoPar a).
      {
        destruct (anno_par t1 loc) eqn: hi.
        erewrite anno_unanno_par.
        reflexivity.
        inversion Heqp0.
        rewrite H0.
        rewrite hi.
        
        simpl.
        
        tauto.
      }
     
      rewrite H0.
       *)
      
      Check cvm_spans.
      Locate cvm_spans.
      eapply cvm_spans; eauto.

    }
    assert (n = i + event_id_span t1).
    {
      
      Check span_range.
      (*
     : forall (t : Term) (i j : nat) (t' : AnnoTerm),
       anno t i = (j, t') -> event_id_span t = j - i
       *)
      assert (event_id_span t1 = n - i).
      {
      
        eapply span_range.
        eassumption.
      }
      rewrite H6.
      assert (n > i).
      {
        eapply anno_mono.
        eassumption.
      }
      lia.

    }
    assert (n = H1) by congruence.
    rewrite H7 in *; clear H7.
    rewrite H6 in *; clear H6.
    assert (t1 = unannoPar a).
    {
      destruct (anno_par t1 loc) eqn: hi.
        erewrite anno_unanno_par.
        reflexivity.
        inversion Heqp0.
        subst.
        rewrite hi.
        simpl.
        tauto.
    }
    subst.
    
    
    
    eassumption.

  - (* abseq case *)


    inversion annoParPH.
    inversion annPH.
    subst.

    
    wrap_ccp.

    assert (n = st_evid1).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      
      eapply span_cvm; eauto.
    }

    assert (n0 = st_evid).
    {
      subst.
      eapply span_cvm; eauto.
    }
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    assert (
        lstar (conf a1 p (splitEv_T_l s et)) blah' (stop p (aeval a1 p (splitEv_T_l s et)))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      destruct s; destruct s; destruct s0;
        simpl in *;
        eauto.
    }

    assert (
      lstar (conf a2 p  (splitEv_T_r s et)) blah (stop p (aeval a2 p  (splitEv_T_r s et)))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      destruct s; destruct s; destruct s0;
        simpl in *; eauto.

    }


    eapply lstar_transitive.
      simpl.

      eapply lstar_stbsl.
      eassumption.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      eassumption.
           
      econstructor.

      eapply stbsrstop.
      econstructor.

  - (* abpar case *)


(*
    

    wrap_ccp.
    
    do_suffix blah.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.
 *)
    inversion annoParPH.
    inversion annPH.
    subst.

    
    wrap_ccp.

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      
      eapply span_cvm; eauto.
    }

    assert (n0 = n + event_id_span t2).
    {
      Check span_range.
      assert (event_id_span t2 = n0 - n).
      {
        eapply span_range.
        eauto.
      }
      assert (n0 > n).
      {
        eapply anno_mono; eauto.
      }
      lia.
    }
    

    (*
    assert (n0 = st_evid).
    {
      subst.
      eapply span_cvm; eauto.
    } *)
    
    repeat do_anno_redo.
    
    do_suffix blah.
    (*
    do_suffix blah'. *)
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a0 p (splitEv_T_l s et)) blah (stop p (aeval a0 p (splitEv_T_l s et)))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      destruct s; destruct s; destruct s0; simpl in *;
        eauto.
    }
    (*
    
      eapply IHt1. apply Heqp0. apply Heqp1.
      eapply IHt1; eauto.
      eapply IHt; eauto.
      eapply IHt; eauto.
    } *)

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start loc p t2 (get_et (splitEv_r s (evc bits et)))]
                ++
                blah ++
                [cvm_thread_end loc] =
              shuffled_events blah (cvm_events t2 p (get_et (splitEv_r s (evc bits et))))).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      jkjke.

      assert (
          (splitEv_T_r s et) =
          (get_et (splitEv_r s (evc bits et)))).
      {
        destruct s; destruct s; destruct s0; ff.
      }
      jkjke.

      assert (t2 = unanno a1).
      {
        invc Heqp2.
        erewrite anno_unanno.
        tauto.
      }
      subst.
      

      eapply lstar_transitive.
      

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      (*
      assert (n0 = st_evid).
      {
        eapply span_cvm.
        


        admit. }
      find_rw_in_goal. *)


      apply stbpstop.
      econstructor.
Defined.

Lemma cvm_refines_lts_event_ordering_corrolary : forall t annt atp cvm_tr bits et p loc i,
    (*well_formed_r_annt t -> *)
    annoP annt t i ->
    anno_parP atp t loc ->
    st_trace (run_cvm atp
                      (mk_st (evc bits et) [] p i)) = cvm_tr ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros.
  destruct (copland_compile atp {| st_ev := (evc bits et); st_trace := []; st_pl := p; st_evid := i |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  do_asome.
  subst.
  
  destruct st_ev.

  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  Check cvm_refines_lts_event_ordering.

  eapply cvm_refines_lts_event_ordering; eauto.
  econstructor; eauto.
Defined.

Theorem cvm_respects_event_system : forall atp annt t cvm_tr ev0 ev1 bits bits' et et' i i' loc,
    (*well_formed_r t -> *)
    annoP annt t i ->
    anno_parP atp t loc ->
    copland_compileP atp
                     (mk_st (evc bits et) [] 0 i)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr 0 i') ->
    prec (ev_sys annt 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  Lemma anno_redo: forall t i annt,
    annoP annt t i ->
    exists i', anno t i = (i', annt).
  Proof.
    intros.
    destruct (anno t i) eqn:hi.
    invc H.
    eexists.
    rewrite hi.
    tauto.
  Defined.

  edestruct anno_redo; eauto.
    

    
  assert (well_formed_r_annt annt).
  eapply anno_well_formed_r.
  eassumption.

  
  eapply ordered.
  eapply anno_well_formed_r.
  eassumption.

  eapply cvm_refines_lts_event_ordering; eauto.
  eassumption.
Defined.


(*
Theorem cvm_respects_event_system : forall pt t cvm_tr ev0 ev1 bits bits' et et' anno_t,
    annoP annt t 0 ->
    anno_parP pt anno_t 0 ->
    copland_compileP pt
                     (mk_st (evc bits et) [] 0)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr 0) ->

    prec (ev_sys anno_t 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.

  assert (well_formed_r pt).
  {
    inversion H0.
    inversion H.
    eapply annopar_well_formed_r.
    unfold annotated.
    rewrite <- H7.
    unfold annotated_par.
    rewrite H3.
    tauto.
  }


  assert (well_formed_r_annt anno_t(*(unannoPar t)*)).
  {
    destruct (anno_par anno_t 0) eqn: hi.
    inversion H0.
    rewrite <- anno_unanno_par with (l:=0) (l':=l) (annt:=pt).
    2: {
      assert (a = pt).
      {
        subst.
        jkjke.
      }
      congruence.
    }
    eapply wfr_implies_wfrannt.
    eassumption.
  }
  eapply ordered; try eassumption.
  assert (anno_t = unannoPar pt).
  {
    destruct (anno_par anno_t 0) eqn: hi.
    inversion H0.
    erewrite anno_unanno_par.
    reflexivity.
    rewrite H5.
    rewrite hi.
    reflexivity.
  }
  rewrite H5.
  eapply cvm_refines_lts_event_ordering; eauto.
Defined.
*)

Theorem cvm_respects_event_system_run : forall atp annt t cvm_tr ev0 ev1 bits (*bits' et' *)et i loc,
    annoP annt t i ->
    anno_parP atp t loc ->
    st_trace (run_cvm atp (mk_st (evc bits et) [] 0 i)) = cvm_tr ->

    (*
    =
    (mk_st (evc bits' et') cvm_tr 0) ->
     *)
    

    prec (ev_sys annt 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  assert (well_formed_r_annt annt).
  {
    edestruct anno_redo.
    eassumption.
    eapply anno_well_formed_r.
    eassumption.
  }

  destruct ((copland_compile atp {| st_ev := evc bits et; st_trace := []; st_pl := 0; st_evid := i |})) eqn:hi.
  do_somett.
  subst.

  simpl in *. destruct c.
  simpl in *.
  unfold run_cvm in *.
  unfold execSt in *.
  rewrite hi.
  simpl.
  destruct st_ev.
  do_pl_immut.
  subst.
  
  eapply cvm_respects_event_system.
  eassumption.
  eassumption.
  econstructor.
  eassumption.
  eassumption.
Defined.

Theorem cvm_respects_event_system_run' : forall atp annt t cvm_tr ev0 ev1 bits (*bits' et' *)et,
    annt = annotated t ->
    atp = annotated_par t ->
    (*
    annoP anno_t t 0 ->
    anno_parP pt anno_t 0 -> *)
    st_trace (run_cvm atp (mk_st (evc bits et) [] 0 0)) = cvm_tr ->

    (*
    =
    (mk_st (evc bits' et') cvm_tr 0) ->
     *)
    

    prec (ev_sys annt 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  eapply cvm_respects_event_system_run.
  econstructor.
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  eassumption.
Defined.
  
