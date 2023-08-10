(*
Helper lemmas for proofs about the CVM semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Anno_Term_Defs Cvm_Monad Cvm_Impl Term_Defs Auto StructTactics AutoApp.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)

Lemma ac_immut : forall t e tr p i ac,
  st_AM_config 
    (execErr 
      (build_cvm t)
      {|
        st_ev := e;
        st_trace := tr;
        st_pl := p;
        st_evid := i;
        st_AM_config := ac
      |}) = ac.
Proof.
  induction t; repeat (monad_unfold; simpl in *); intuition.
  - destruct a; monad_unfold; eauto.
    destruct a0.
    destruct (do_asp' a (get_bits e) p i
             {| st_ev := e; st_trace := tr ++ [umeas i p a (get_et e)]; st_pl := p; st_evid := i + 1; st_AM_config := ac |}), r; simpl in *; eauto.
  - monad_unfold; simpl in *.
    pose proof (IHt1 e tr p i ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *.
    pose proof (IHt2 st_ev st_trace st_pl st_evid st_AM_config).
    destruct (build_cvm t2 {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config |}) eqn:C2;
    simpl in *; subst; eauto.
  - monad_unfold; simpl in *.
    pose proof (IHt1 e (tr ++ [Term_Defs.split i p]) p (i + 1) ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr ++ [Term_Defs.split i p]; st_pl := p; st_evid := (i + 1); st_AM_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *.
    pose proof (IHt2 e st_trace st_pl st_evid st_AM_config).
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config |}) eqn:C2;
    simpl in *; subst; eauto;
    destruct r; simpl in *; eauto.
  - monad_unfold; simpl in *.
    pose proof (IHt1 e ((tr ++ [Term_Defs.split i p]) ++ [cvm_thread_start l p t2 (get_et e)]) p (i + 1) ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := (tr ++ [Term_Defs.split i p]) ++ [cvm_thread_start l p t2 (get_et e)]; st_pl := p; st_evid := (i + 1); st_AM_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *; eauto.
Qed.

(* Lemma stating the CVM st_pl parameter ends up where it started execution *)
Lemma pl_immut : forall t e tr p i ac,
    st_pl
      (execErr
         (build_cvm t)
         {|
           st_ev := e;
           st_trace := tr;
           st_pl := p;
           st_evid := i;
           st_AM_config := ac |}) = p.
Proof.
  induction t; intros.
  -
    destruct a; (* asp *)
      try destruct a; (* asp params *)    
      try reflexivity; simpl in *.
      destruct ac.
      unfold invoke_ASP.
      monad_unfold.
      unfold do_asp'.
      simpl in *.
      destruct (aspCb (asp_paramsC a l p0 t) p (encodeEvRaw (get_bits e)) (get_bits e)); simpl in *; eauto.

  -
    df.
    reflexivity.
  -
    simpl in *.
    monad_unfold.
    repeat break_match;
      try solve_by_inversion.
    df.
    annogo.
    simpl.  
    assert (p = st_pl0).
    {
      edestruct IHt1.
      jkjke.
    }
    subst.
    pose proof (ac_immut t2 st_ev0 st_trace0 st_pl0 st_evid0 st_AM_config0).
    pose proof (IHt2 st_ev0 st_trace0 st_pl0 st_evid0 st_AM_config0); simpl in *.
    destruct (build_cvm t2) eqn:C2.
    unfold execErr in *.
    rewrite C2 in *; simpl in *; eauto;
    inversion Heqp1; subst; simpl in *; eauto.
  -
    (*
    do_wf_pieces. *)
    annogo.
    df.
    
    repeat break_match;
      try solve_by_inversion;
    repeat find_inversion;
    repeat dunit;
    simpl in *; vmsts; simpl in *.
    +
    assert (p = st_pl0).
    {
      edestruct IHt1.
      jkjk_s; eauto.     
    }

    assert (st_pl0 = st_pl).
    {     
      edestruct IHt2.
      jkjk_s; eauto.
    }

    congruence.
    +
      assert (p = st_pl0).
      {
        edestruct IHt1.
        jkjk_s; eauto.
      }

      assert (st_pl0 = st_pl).
      {
        edestruct IHt2.
        jkjk_s; eauto.
      }

      congruence.
    +
    assert (p = st_pl).
    {
      edestruct IHt1.
      jkjk_s; eauto.
    }

    assert (st_pl = st_pl0).
    {
      edestruct IHt2.
      jkjk_s; eauto.
    }

    congruence.

    +
    assert (p = st_pl0).
    {
      edestruct IHt1.
      jkjk_s; eauto.
    }

    assert (st_pl0 = st_pl).
    {
      edestruct IHt2.
      jkjk_s; eauto.
    }

    congruence.



  -
    annogo.
    df.

    repeat break_let.

    repeat break_match;
      try solve_by_inversion;
    repeat find_inversion;
    repeat dunit;
    simpl in * ; vmsts; simpl in *.
    +
    assert (p = st_pl).
    {
      edestruct IHt1.
      jkjke. 
    }
    congruence.   

    +
    assert (p = st_pl).
    {
      edestruct IHt1.
      jkjke.    
    }
    congruence. 
Defined.

Ltac do_pl_immut :=
  let tac H :=
       erewrite <- pl_immut;
        [ unfold execErr;
          rewrite H;
          reflexivity (*| 
          apply H2*)] in
      match goal with
      | [H: build_cvm ?t
                            {| st_ev := _;
                        st_trace := _;
                                    st_pl := ?p;
                            st_evid := _|} =
            (_,
             {| st_ev := _;
                         st_trace := _;
                         st_pl := ?p'; st_evid := _ |})
         (*H2: well_formed_r ?t*) |- _] =>
        assert_new_proof_by (p' = p) ltac:(tac H)  
      end.

Lemma st_congr :
  forall st tr e p i ac,
    st_ev st = e ->
    st_trace st = tr ->
    st_pl st = p ->
    st_evid st = i ->
    st_AM_config st = ac ->
    st =  {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |}.
Proof.
  intros.
  subst; destruct st; auto.
Defined.

(* Hack to apply a specific induction hypothesis in some proofs *)
Ltac anhl :=
  annogo;
  match goal with
  | [H2: build_cvm ?a _ = _,
     H3: build_cvm ?a _ = _,
     IH: context[ _ -> _] |- _] =>
    edestruct IH;
    [ apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

(* Lemma stating the following:  If all starting parameters to the cvm_st are the same, except 
   for possibly the trace, then all of those final parameters should also be equal. *)
Lemma st_trace_irrel : forall t e e' e'' x x' y y' p p' p'' i i' i'' ac ac' ac'',
    build_cvm t {| st_ev := e; st_trace := x; st_pl := p; st_evid := i; st_AM_config := ac |} =
    (resultC tt, {| st_ev := e'; st_trace := x'; st_pl := p'; st_evid := i'; st_AM_config := ac' |}) ->
    build_cvm t {| st_ev := e; st_trace := y; st_pl := p; st_evid := i; st_AM_config := ac |} =
    (resultC tt, {| st_ev := e''; st_trace := y'; st_pl := p''; st_evid := i''; st_AM_config := ac'' |}) ->
    (e' = e'' /\ p' = p'' /\ i' = i'' /\ ac' = ac'').
Proof.
  induction t; intros.
  - destruct a; (* asp *)
      try destruct a; (* asp params *)
      df; eauto.
    unfold do_asp' in *;
    destruct (do_asp (asp_paramsC a l p0 t) (get_bits e) p i ac);
    monad_unfold; simpl in *;
    invc Heqp11; invc Heqp5; invc Heqp4; invc Heqp10; simpl in *;
    try congruence;
    invc H; invc H0; eauto.
  -
    repeat (df; try dohtac; df).
    tauto.
  -
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    anhl.
    eauto. 
  -
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    repeat anhl.
    repeat find_inversion.
    eauto.
  -
    cbn in *.
    monad_unfold.
    repeat break_let.
    simpl in *.

    dosome.
    df.
    dosome.
    dosome.
    df.

    ff.

    (*
    annogo.
    simpl in *.
    ff. *)

    repeat anhl.
    repeat (find_inversion).
    repeat find_rewrite.
    df.
    tauto.
Defined.


Ltac dohi'' :=
  annogo;
  let tac H H' := eapply st_trace_irrel; [apply H | apply H'] in
  match goal with
  | [H : build_cvm ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |} =
         (?opt, {| st_ev := ?e'; st_trace := _; st_pl := ?p'; st_evid := ?i'; st_AM_config := ?ac' |}),
         H' : build_cvm ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |} =
              (?opt, {| st_ev := ?e''; st_trace := _; st_pl := ?p''; st_evid := ?i''; st_AM_config := ?ac'' |})
     |- _] =>
    assert_new_proof_by (e' = e'' /\ p' = p'' /\ i' = i'' /\ ac' = ac'') ltac:(tac H H')
  end.

Ltac dohi :=
  do 2 (repeat dohi''; destruct_conjs; subst);
  repeat clear_triv.

Ltac do_st_trace :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |}]
     |- context[?tr]] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |} )
      tauto
  end.

Ltac do_st_trace_assumps :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |}]
     |- _] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |} )
      tauto
  end.

Ltac find_rw_in_goal :=
  match goal with
  | [H': context[?x = _]
     |- context[?x]] =>
    rewrite H'; clear H'
  end.

Inductive build_cvmP :
  Core_Term -> cvm_st -> (ResultT unit CVM_Error) -> cvm_st ->  Prop :=
| ccp: forall t st st' res,
    build_cvm t st = (res, st') ->
    build_cvmP t st res st'.

Lemma ccp_implies_cc: forall t st st' res,
  build_cvmP t st res st' ->
  build_cvm t st = (res,st').
Proof.
  intros.
  solve_by_inversion.
Defined.

Lemma cc_implies_ccp: forall t st st' res,
  build_cvm t st = (res,st') -> 
  build_cvmP t st res st'.
Proof.
  intros.
  econstructor.
  tauto.
Defined.

Lemma ccp_iff_cc: forall t st st' res,
  build_cvm t st = (res,st') <-> 
  build_cvmP t st res st'.
Proof.
  intros.
  split; intros;
    try (eapply cc_implies_ccp; eauto);
    try (eapply ccp_implies_cc; eauto).
Defined.

Ltac inv_term_coreP :=
  match goal with
  | [H: term_to_coreP _ _ (* ?t (?c _) *)
     |- _ ] =>
    inversion H; subst
  end.

Lemma term_to_coreP_redo: forall t t',
    copland_compile t = t' ->
    term_to_coreP t t'.
Proof.
  intros.
  econstructor.
  eauto.
Defined.

Ltac do_term_to_core_redo :=
  match goal with
  | [H: copland_compile ?t = ?t'
     |- _ ] =>
    eapply term_to_coreP_redo in H
  end.



Lemma annoP_redo: forall t annt n n',
    anno t n = (n', annt) ->
    annoP annt t.
Proof.
  intros.
  econstructor.
  eexists.
  jkjke.
Defined.

Ltac do_anno_redo :=
  match goal with
  | [H: anno ?t ?n = (_,?annt)
     |- _ ] =>
    eapply annoP_redo in H
  end.

Ltac inv_annoP :=
  match goal with
  | [H: annoP _ _ (*_ (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Lemma annoP_indexed_redo: forall t annt n n',
    anno t n = (n', annt) ->
    annoP_indexed annt t n n'.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.

Ltac do_anno_indexed_redo :=
  match goal with
  | [H: anno _ _ = (_,_)
     |- _ ] =>
    eapply annoP_indexed_redo in H
  end.

Ltac inv_annoP_indexed :=
  match goal with
  | [H: annoP_indexed _ _ _ _(*_ (?c _) _*)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Ltac wrap_annopar :=
  inv_term_coreP;
  dd;
  repeat do_term_to_core_redo.

Ltac wrap_anno :=
  inv_annoP;
  dd;
  repeat do_anno_redo.

Ltac wrap_anno_indexed :=
  inv_annoP_indexed;
  dd;
  repeat do_anno_indexed_redo.

Ltac wrap_ccp :=
  
  try rewrite <- ccp_iff_cc in *;
  dd;
  repeat do_pl_immut;
  dd;
  try rewrite ccp_iff_cc in *.

Ltac wrap_ccp_anno :=
  
  try rewrite <- ccp_iff_cc in *;
  try wrap_annopar;
  try wrap_anno;
  try wrap_anno_indexed;
  repeat do_pl_immut;
  try (unfold OptMonad_Coq.ret in * );
  try (unfold OptMonad_Coq.bind in * );
  try (unfold ErrorStMonad_Coq.bind in * );
  try (unfold ErrorStMonad_Coq.ret in * );
  dd;
  try rewrite ccp_iff_cc in *.



Ltac cumul_ih :=
  match goal with
  | [H: context[(st_trace _ = _ ++ st_trace _)],
        H': build_cvmP ?t1 {| st_ev := _; st_trace := ?m ++ ?k; st_pl := _; st_evid := _; st_AM_config := _ |}
                             (resultC tt)
                             ?v_full,
            H'': build_cvmP ?t1 {| st_ev := _; st_trace := ?k; st_pl := _; st_evid := _; st_AM_config := _ |}
                                  (resultC tt)
                                  ?v_suffix
     |- _] =>
    assert_new_proof_by (st_trace v_full = m ++ st_trace v_suffix) eauto
  end.

Ltac wrap_ccp_dohi :=
  rewrite <- ccp_iff_cc in *;
  dd;
  dohi;
  rewrite ccp_iff_cc in *.
