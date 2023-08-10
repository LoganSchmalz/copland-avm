Require Import ConcreteEvidence AutoApp Auto Helpers_CvmSemantics Term_Defs Anno_Term_Defs Cvm_St Cvm_Impl Defs StructTactics OptMonad_Coq IO_Stubs Evidence_Bundlers Axioms_Io External_Facts. (* Cvm_Monad *)

(* Require Import ErrorStMonad_Coq. *)
Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics.


Definition peel_bs (ls:RawEv) : Opt (BS * RawEv) :=
  match ls with
  | bs :: ls' => OptMonad_Coq.ret (bs, ls')
  | _ => OptMonad_Coq.failm
  end.

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

Fixpoint encodeEv (e:EvidenceC) : RawEv :=
  match e with
  | mtc => []
  | nnc _ bs => [bs]
  | ggc _ _ bs e' => bs :: (encodeEv e')
  | hhc _ _ bs _ => [bs]
  | eec _ _ bs _ => [bs]
  | kkc _ _ _ => []
  | kpc _ _ e' => encodeEv e'
  | ssc e1 e2 => (encodeEv e1) ++ (encodeEv e2)
  end.

Fixpoint reconstruct_ev' (ls:RawEv) (et:Evidence) : Opt EvidenceC :=
  match et with
  | mt => 
    match ls with
    | [] => Some mtc
    | _ => None
    end
  | uu p fwd ps et' =>
    match fwd with
    | EXTD => 
      '(bs, ls') <- peel_bs ls ;;
      x <- reconstruct_ev' ls' et' ;;
      Some (ggc p ps bs x)
    | COMP =>
      '(bs, ls') <- peel_bs ls ;;
      match ls' with
      | [] => Some (hhc p ps bs et')
      | _ => None
      end
    | ENCR =>
      '(bs, ls') <- peel_bs ls ;;
      match ls' with
      | [] => Some (eec p ps bs et')
      | _ => None
      end
    | KILL =>
      match ls with
      | [] => Some (kkc p ps et')
      | _ => None
      end
    | KEEP =>
      x <- reconstruct_ev' ls et' ;;
      Some (kpc p ps x)
    end
  | nn i =>
    '(bs, ls') <- peel_bs ls ;;
     match ls' with
    | [] => Some (nnc i bs)
    | _ => None
    end 
  | ss et1 et2 =>
    e1 <- reconstruct_ev' (firstn (et_size et1) ls) et1 ;;
    e2 <- reconstruct_ev' (skipn (et_size et1) ls) et2 ;;
    Some (ssc e1 e2)
  end.

Definition reconstruct_ev (e:EvC) : Opt EvidenceC :=
  match e with
  | evc ls et => reconstruct_ev' ls et
  end.

Inductive reconstruct_evP: EvC -> EvidenceC -> Prop :=
| reconstruct_evC: forall e ee,
    Some ee = reconstruct_ev e ->
    reconstruct_evP e ee.


Lemma inv_recon_mt: forall ls et,
    reconstruct_evP (evc ls et) mtc ->
    (et = mt) (* \/ (exists p ps et', et = uu p KILL ps et')
    \/ (exists p ps et', et = uu p KEEP ps et')) *) .
Proof.
  intros.
  invc H.
  destruct et;
    repeat ff;
    try (unfold OptMonad_Coq.bind in *);
         repeat ff;
         try solve_by_inversion.
                    
         -
           eauto.
           (*
         -
           right.
           right.
           eauto. *)
                                   
Defined.

Ltac do_inv_recon_mt :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) mtc

     |- _] =>
    assert_new_proof_by (et = mt (* \/ (exists p ps et', et = uu p KILL ps et') \/ (exists p ps et', et = uu p KEEP ps et') *) ) ltac:(eapply inv_recon_mt; apply H)
  end;
  (* door; *)
  subst.

Lemma inv_recon_mt': forall ls e,
    reconstruct_evP (evc ls mt) e ->
    e = mtc.
Proof.
  intros.
  invc H.
  repeat ff; try solve_by_inversion; eauto.
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
    ((et = nn n /\ ls = [n0]) (* \/ (exists p ps et', et = uu p KEEP ps et') *) ).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.

                               (*
                               -
                                 eauto.
                               -
                                 eauto. *)
                                 
                                 
Defined.

Ltac do_inv_recon_nn :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (nnc ?n ?nval)

     |- _] =>
    assert_new_proof_by (et = nn n /\ ls = [nval] (* \/ (exists p ps et', et = uu p KEEP ps et') *) ) ltac:(eapply inv_recon_nn; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_gg: forall p ps ls et n ec,
    reconstruct_evP (evc ls et) (ggc p ps n ec) ->
    (exists ls' et', et = uu p EXTD ps et' /\
                ls = n :: ls') (* \/ (exists p ps et', et = uu p KEEP ps et') *) .
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; try solve_by_inversion.
                               -
                                 (*
                                 left. *)
                                 repeat eexists.
                                 destruct ls; ff.
                                 (*
                               -
                                 right.
                                 eauto. *)
                                 
Defined.

Ltac do_inv_recon_gg :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (ggc ?p ?ps ?n _)

     |- _] =>
    assert_new_proof_by ((exists ls' et', et = uu p EXTD ps et' /\
                                    ls = n :: ls') (* \/ (exists p ps et', et = uu p KEEP ps et') *) )
                        ltac:(eapply inv_recon_gg; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_hh: forall p ps ls et n et',
    reconstruct_evP (evc ls et) (hhc p ps n et') ->
    ((et = uu p COMP ps et' ) /\ ls = [n]) (* \/ (exists p ps et', et = uu p KEEP ps et') *) .
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.
                               (*
                               -
                                 right. eauto.
                               -
                                 right. eauto. *)
                                 
                                 
Defined.

Ltac do_inv_recon_hh :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (hhc ?p ?ps ?hval ?et')

     |- _] =>
    assert_new_proof_by ((et = uu p COMP ps et' /\ ls = [hval]) (* \/ (exists p ps et', et = uu p KEEP ps et') *) )
                        ltac:(eapply inv_recon_hh; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ee: forall p ps ls et (*et'*) n ec',
    reconstruct_evP (evc ls et) (eec p ps n (*et'*) ec') ->
    (* (exists et', et = uu p ENCR ps et' ) /\ ls = [n]. *)
    (exists et', et = uu p ENCR ps et' /\ ls = [n]) (* \/ (exists p ps et', et = uu p KEEP ps et') *) .
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; destruct ls; try solve_by_inversion.
                               -
                                 (*
                                 left. *)
                               repeat eexists.
                               ff.
                               (*
                               -
                                 right. eauto.
                               -
                                 right. eauto. *)
                                 
                                 
                               
Defined.

Ltac do_inv_recon_ee :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (eec ?p ?ps ?hval (*_*) _)

     |- _] =>
    assert_new_proof_by ( (exists et', et = uu p ENCR ps et' /\ ls = [hval]) (* \/ (exists p ps et', et = uu p KEEP ps et') *) )
                        ltac:(eapply inv_recon_ee; apply H)
  end;
  destruct_conjs;
  subst.

(*
Lemma inv_recon_kk: forall p ps ls et et',
    reconstruct_evP (evc ls et) (kkc p ps et') ->
    (et = uu p KILL ps et' ) /\ ls = [].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_kk :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (kkc ?p ?ps ?et')

     |- _] =>
    assert_new_proof_by (et = uu p KILL ps et' /\ ls = [])
                        ltac:(eapply inv_recon_kk; apply H)
  end;
  destruct_conjs;
  subst.
*)

Lemma inv_recon_ss: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ssc ec1 ec2) ->
    (exists et1 et2, et = ss et1 et2) (* \/ (exists p ps et', et = uu p KEEP ps et') *) .
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff; try solve_by_inversion.
                               -
                                 (*
                                 right. *)  eauto.
                                            (* 
                               -
                               left. eauto.
                                             *)
                                            
Defined.

Ltac do_inv_recon_ss :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ssc _ _)

     |- _] =>
    assert_new_proof_by ((exists et1 et2, et = ss et1 et2) (* \/ (exists p ps et', et = uu p KEEP ps et') *) )
                        ltac:(eapply inv_recon_ss; apply H)
  end;
  destruct_conjs;
  subst.


Ltac do_inv_recon :=
  try do_inv_recon_mt;
  try do_inv_recon_mt';
  try do_inv_recon_nn;
  try do_inv_recon_gg;
  try do_inv_recon_hh;
  try do_inv_recon_ee;
  (* try do_inv_recon_kk; *)
  try do_inv_recon_ss.

Lemma recon_inv_gg: forall sig ls p ps et e,
    reconstruct_evP
      (evc (sig :: ls) (uu p EXTD ps et))
      (ggc p ps sig e) ->
    reconstruct_evP (evc ls et) e.
Proof.
  intros.
  invc H.
  repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff;
  econstructor.
  symmetry.
  tauto.
Defined.

Ltac do_recon_inv_gg :=
  match goal with
  | [H: reconstruct_evP
          (evc (_ :: ?ls) (uu _ _ _ ?et))
          (ggc _ _ _ ?e)
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
  repeat ff; try (unfold OptMonad_Coq.bind in *); repeat ff;
  split;
    econstructor;
    try 
      symmetry; eassumption.
Qed.

Ltac do_recon_inv_ss :=
  match goal with
  | [H: reconstruct_evP
          (evc ?ls (ss ?H1 ?H2))
          (ssc ?ec1 ?ec2) _
     |- _] =>
    assert_new_proof_by
      (reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
       reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2)
      ltac:(eapply recon_inv_ss; apply H)
  end; destruct_conjs.

Ltac do_recon_inv :=
  try do_recon_inv_gg;
  try do_recon_inv_ss.


Lemma wrap_reconP: forall ec e,
    reconstruct_ev ec = Some e ->
    reconstruct_evP ec e.
Proof.
  intros.
  econstructor.
  congruence.
Defined.

Lemma fold_recev: forall e0 e1,
    reconstruct_ev' e0 e1 = reconstruct_ev (evc e0 e1).
Proof.
  ff.
  tauto.
Defined.

Ltac do_wrap_reconP :=
  repeat
  match goal with
  | [H: reconstruct_ev ?ec = Some ?e
     |- _] =>
    apply wrap_reconP in H
  end.

Ltac do_rewrap_reconP :=
  match goal with
  | [H: reconstruct_evP (evc _ (?cc _)) _
     |- _] =>
    invc H;
    repeat ff;
    try rewrite fold_recev in *;
    do_wrap_reconP
  end.


(*
TODO: try this again after appraisal lemmas settled 
*)

Lemma etfun_reconstruct: forall e e0 e1,
    reconstruct_evP (evc e0 e1) e ->
    e1 = et_fun e (* \/ (exists p ps et', e1 = uu p KEEP ps et' /\ et' = et_fun e) *) .
Proof.
  intros.
  generalizeEverythingElse e1.

  (*
  induction e1; intros e e0 H;
    do_inv_recon;
    ff.
  -
    invc H.
    repeat ff;
      try (unfold OptMonad_Coq.bind in * );
           repeat ff.
  -
    invc H;
      ff;
      try (unfold OptMonad_Coq.bind in * );
      destruct f;    try (unfold OptMonad_Coq.bind in * );
      try (ff; tauto).
    +
      ff.
      assert (e1 = et_fun e2).
      eapply IHe1.
      econstructor; eauto.
      subst.
      tauto.
    +
      ff.
      
      
      
      
      
      eauto.
      tauto.
    ff.
    repeat ff;
      try (unfold OptMonad_Coq.bind in * );
           repeat ff.
           +
             assert (e1 = et_fun e2).
             eapply IHe1.
             econstructor; eauto.
             subst.
             tauto.
           +

             Locate et_fun.
             Locate reconstruct_ev.
             
 *)
             
             
                      
   


  
  induction e1; intros e e0 H.
  - (* mt case *)
    invc H.
    ff.
    tauto.
  - (* nn case *)
    invc H.
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    
    
    

  (* 
    try (
    do_inv_recon;
    ff;
    invc H;
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff;
    rewrite fold_recev in *;
    do_wrap_reconP;
    repeat jkjke).
   *)
  
  - (* uu case *)
    destruct f; ff.
    + (* COMP case *)
      invc H.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    + (* ENCR case *)
      (*
      Print et_fun.
      Print do_inv_recon_ee.
      Print do_inv_recon_ee.
      Locate reconstruct_ev.
       *)
      
      invc H.
      unfold reconstruct_ev in *.
      unfold reconstruct_ev' in *.
      unfold OptMonad_Coq.bind in *.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
           
    + (* EXTD case *)
      (* left. *)
      invc H.
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      assert (e1 = et_fun e2 (* \/ (exists (p : Plc) (ps : ASP_PARAMS) (et' : Evidence),
                                   e1 = uu p KEEP ps et' /\ et' = et_fun e2) *) ).
      {
      eapply IHe1.
      econstructor.
      ff.
      }
      (*
      door.
      ++ *)
        
      congruence.
      (*
      ++
        
        
      subst.
      
      
      congruence. *)
    + (* KILL case *)
      invc H.
      unfold reconstruct_ev in *.
      ff.
    + (* KEEP case *)
      invc H.
      unfold reconstruct_ev in *.
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      assert (e1 = et_fun e2).
      { eapply IHe1.
        econstructor.
        unfold reconstruct_ev.
        symmetry.
        eassumption.
      }
      subst.
      tauto.
  - (* ss case *)
    invc H.
    ff.
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    assert (e1_1 = et_fun e1).
    {
      eapply IHe1_1.
      econstructor.
      symmetry.
      eassumption.
    }
    assert (e1_2 = et_fun e2).
    {
      eapply IHe1_2.
      econstructor.
      symmetry.
      eassumption.
    }
    congruence.
Qed.

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




(* Lemma:  Encoding an EvC bundle gives you the bits used 
   to (re)construct it. *)
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
    repeat ff.
    (*
    invc H.
    repeat ff. *)
  - (* nnc case *)
    do_inv_recon.
    ff.
  - (* ggc case *)
    do_inv_recon.
    ff.
    invc H.
    repeat ff.
    unfold OptMonad_Coq.bind in *.
    ff.
    assert (reconstruct_evP (evc H0 H1) e).
    {
      econstructor; eauto.
    }
    assert (encodeEv e = H0) by eauto.
    congruence.
  - (* hhc case *)
    do_inv_recon.
    ff.
  - (* eec case *)
    
    do_inv_recon.
    ff.

    (*
  -
    do_inv_recon.
    ff. 
     *)

  - (* kkc case *)
    do_inv_recon.
    ff.
    invc H.
    ff.
    unfold reconstruct_ev' in *.
    ff.
    unfold OptMonad_Coq.bind in *.
    ff.
    rewrite fold_recev in *.
    unfold reconstruct_ev in *.
    unfold reconstruct_ev' in *.
    destruct et; try solve_by_inversion.
    ff.
    unfold OptMonad_Coq.bind in *.
    ff.
    unfold OptMonad_Coq.bind in *.
    ff.
    unfold OptMonad_Coq.bind in *.
    ff.


  - (* kpc case *)
    ff.

    assert (exists et', et = uu p KEEP a et').
    {
      destruct et; try solve_by_inversion.
      +
        invc H.
        ff.
      +
        invc H.
        ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      +
        invc H.
        ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
        eexists.
        tauto.
      +
        invc H.
        ff.
        repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    }
    
    destruct_conjs.
    subst.

    invc H.
    ff.
    repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    eapply IHec.
    econstructor.
    ff.
    
    
    
    
    
    
  - (* ssc case *)
    do_inv_recon.
    ff.
    invc H.
    ff.
    unfold OptMonad_Coq.bind in *.
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
Qed.

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

Lemma wfec_recon: forall (ee:EvC) (ec:EvidenceC),
    reconstruct_evP ee ec ->
    wf_ec ee.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros; destruct ee.
  - (* mtc case *)
    do_inv_recon.
    dd.
    invc H.
    dd.
    ff.
    econstructor. tauto.
    (* 
    invc H.
    repeat ff. *)
    (*
    econstructor. tauto. *)
  - (* nnc case *)
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
  - (* ggc case *)
    do_inv_recon.
    invc H.
    dd.
    ff.
    unfold OptMonad_Coq.bind in *.
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

  - (* hhc case *)
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
  - (* eec case *)
    do_inv_recon.
    invc H.
    dd.
    econstructor; tauto.
    (*
  -
    do_inv_recon.
    invc H.
    econstructor; tauto.   
     *)

  - (* kkc case *)
    invc H.
    unfold reconstruct_ev in *.
    unfold reconstruct_ev' in *.
    destruct e0; try solve_by_inversion.
    ff.
    unfold OptMonad_Coq.bind in *. ff.
    unfold OptMonad_Coq.bind in *. ff.
    econstructor.
    ff.
    unfold OptMonad_Coq.bind in *. ff.
  - (* kpc case *)
    invc H.
    destruct e; try solve_by_inversion.
    +
      ff.
    +
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
    +
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
      assert (wf_ec (evc r e)).
      {
        eapply IHec. econstructor.
        symmetry. eassumption. }
      econstructor.
      ff.
    +
      ff.
      repeat ff; try (unfold OptMonad_Coq.bind in * ); repeat ff.
   
  -
    do_inv_recon.
    invc H.
    dd.
    ff.
    unfold OptMonad_Coq.bind in *.
    
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
    assert (r = firstn (et_size H0) r ++ skipn (et_size H0) r).
    {
      symmetry.
      eapply firstn_skipn.
    }
    rewrite H at 1.
    eapply app_length.
Qed.

Lemma reconP_determ: forall ec e e',
    reconstruct_evP ec e ->
    reconstruct_evP ec e' ->
    e = e'.
Proof.
  intros.
  invc H; invc H0.
  repeat jkjke'.
  ff.
Defined.

Ltac do_reconP_determ :=
  repeat 
  match goal with
  | [H: reconstruct_evP ?ec ?e,
        H2: reconstruct_evP ?ec ?e2
     |- _] =>
    assert_new_proof_by (e = e2)
                        ltac:(eapply reconP_determ; [apply H | apply H2]);
    clear H2
  end; subst.



Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
    end.

(** * If a raw evidence sequence is non-empty, we can grab a first element. *)
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

(** * Lemma:  well-formed EvC bundles can be successfully reconstructed to a Typed Concrete Evidence (EvidenceC) value. *)
Lemma some_recons : forall (e:EvC),
    wf_ec e ->
    exists (ee:EvidenceC), Some ee = reconstruct_ev e.
Proof.
  intros.
  destruct e.
  generalizeEverythingElse e.
  induction e; intros.
  -
  try (repeat ff; eauto; tauto).
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
          repeat jkjke';
          repeat ff; eauto).

  - (* nn case *)
    repeat ff.
    (unfold OptMonad_Coq.bind in * ).
     repeat ff.
     +
     eauto.
     +
       inv_wfec.
       ff.
       destruct r; try solve_by_inversion.
       ff.
       unfold OptMonad_Coq.ret in *.
       repeat ff.
       

     +
       destruct r; try solve_by_inversion.
       ff.
       invc H.
       ff.


    
  - (* uu case *)

    destruct f.
    
    + (* COMP case *)

      inv_wfec.
      ff.
      repeat ff;
    (unfold OptMonad_Coq.bind in * );
    repeat ff; eauto.

      ++
       ff.
       assert (exists v, r = [v]).
       {
         destruct r; ff.
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
      ++
       assert (exists v, r = [v]).
       {
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
    + (* ENCR case *)

      inv_wfec.
      ff.
      repeat ff;
    (unfold OptMonad_Coq.bind in * );
    repeat ff; eauto.
      ++
         ff.
       assert (exists v, r = [v]).
       {
         destruct r; ff.
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
      ++
       assert (exists v, r = [v]).
       {
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
    + (* EXTD case *)
      inv_wfec.
      ff.
      unfold OptMonad_Coq.bind in * ;
        repeat ff; eauto.
      ++
        assert (wf_ec (evc r0 e)).
        {
          eapply peel_fact.
          eassumption.
          eassumption.
          tauto.
        }
       
          
          
        assert (exists ee, Some ee = reconstruct_ev' r0 e).
        {
          invc H.
          eapply IHe.
         econstructor. eassumption. }
        destruct_conjs.
        ff.
      ++
         inv_wfec.
       ff.
       assert (r = []).
       {
         destruct r; ff.
       }
       subst.
       ff.
    + (* KILL case *)
      inv_wfec.
      ff.
      eauto.
    + (* KEEP case *)
      inv_wfec.
      simpl in H1.
      ff.

    repeat ff;
    (unfold OptMonad_Coq.bind in * );
    repeat ff; eauto.
    assert (exists ee, Some ee = reconstruct_ev' r e).
    { eapply IHe.
      econstructor.
      eassumption.
    }
    destruct_conjs.
    congruence.




    (*



    
     +
       inv_wfec.
       ff.
       assert (exists v, r = [v]).
       {
         destruct r; ff.
         destruct r; ff. }
       destruct_conjs. subst.
       ff.
     +
       inv_wfec.
       assert (r = []).
       {
         destruct r; ff. }
       subst.
       ff.
     +
       inv_wfec.
       ff.
       assert (exists v, r = [v]).
       { destruct r; ff.
       destruct r; ff. }
       destruct_conjs.
       subst.
       ff.
     +
       inv_wfec.
       ff.
       assert (exists v, r = [v]).
       { destruct r; ff. }
       destruct_conjs.
       subst.
       ff.
     +
       inv_wfec.
       ff.
       destruct r; ff.
       unfold OptMonad_Coq.ret in *.
       ff.
       assert (exists ee, Some ee = reconstruct_ev' r0 e).
       { eapply IHe.
         econstructor. eassumption. }
       destruct_conjs.
       rewrite <- H1 in *.
       solve_by_inversion.
     +
       inv_wfec.
       ff.
       assert (r = []).
       {
         destruct r; ff.
       }
       subst.
       ff.
     +
       inv_wfec.
       ff.
       
       
       
       
       
       
      (* 
       
       
     
     +
       inv_wfec.
       ff.
       eapply peel_fact.
     eauto.
     +
       inv_wfec.
       assert (wf_ec (evc r0 e)).
       {
         eapply peel_fact; eauto.
       }
       ff.
     +
       destruct r; try solve_by_inversion.
       ff.
       invc H.
       ff.

         -
    repeat ff.
    (unfold OptMonad_Coq.bind in * ).
     repeat ff.
     +
     eauto.
     +
       inv_wfec.
       ff.
       destruct r; try solve_by_inversion.
       ff.
       unfold OptMonad_Coq.ret in *.
       repeat ff.
       

     +
       destruct r; try solve_by_inversion.
       ff.
       invc H.
       ff.
       *)
     +
       inv_wfec.
       ff.
       edestruct IHe.
       econstructor.
       eassumption.
       asdf
       
       *)
         
       
    
     - (* ss case *)
       try (ff; eauto; tauto).
       inv_wfec; ff.
    do_rcih.
    do_rcih.
    destruct_conjs.
    jkjke'.
    jkjke'.
    ff.
    eauto.
Qed.

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

Definition spc_ev (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.

(*
TODO: try this again after appraisal lemmas settled 
*)
Require Import ErrorStMonad_Coq.


Definition cvm_evidence_denote_asp (a:ASP) (p:Plc) (e:EvidenceC) (x:Event_ID) (ac : AM_Config): EvidenceC :=
  match a with
  | NULL => mtc
  | CPY => e
  | ASPC sp fwd params =>
    match (do_asp params (encodeEv (spc_ev sp e)) p x ac) with
    | resultC bs => 
        match fwd with
        | COMP => hhc p params bs (sp_ev sp (et_fun e))
        | EXTD => ggc p params bs (spc_ev sp e)
        | ENCR => eec p params bs (sp_ev sp (et_fun e))
        | KEEP => (spc_ev sp e)
        | KILL => mtc (* kkc p params (sp_ev sp (et_fun e)) *)
        end
    | errC e => mtc
    end
  | SIG => 
      match (do_asp sig_params (encodeEv e) p x ac) with
      | resultC bs => ggc p sig_params bs e
      | errC e => mtc
      end
  | HSH => 
      match (do_asp hsh_params (encodeEv e) p x ac) with
      | resultC bs => hhc p hsh_params bs (et_fun e)
      | errC e => mtc
      end
  | ENC q => 
      match (do_asp (enc_params q) (encodeEv e) p x ac) with
      | resultC bs => eec p (enc_params q) bs (et_fun e)
      | errC e => mtc
      end
  end.


(** * Denotation function of a Typed Concrete Evidence value from an annotated term, initial place, initial evidence *)
Fixpoint cvm_evidence_denote (t:AnnoTerm) (p:Plc) (ec:EvidenceC) (ac : AM_Config) : EvidenceC :=
  match t with
  | aasp (i,_) x => cvm_evidence_denote_asp x p ec i ac
  | aatt _ q x => cvm_evidence_denote x q ec ac
  | alseq _ t1 t2 => cvm_evidence_denote t2 p (cvm_evidence_denote t1 p ec ac) ac
  | abseq _ s t1 t2 => ssc (cvm_evidence_denote t1 p ((splitEvl s ec)) ac)
                         (cvm_evidence_denote t2 p ((splitEvr s ec)) ac)
  | abpar _ s t1 t2 => ssc (cvm_evidence_denote t1 p ((splitEvl s ec)) ac)
                         (cvm_evidence_denote t2 p ((splitEvr s ec)) ac)
  end.


(** * Assert an arbitrary (remote) CVM execution.  
      Uses uninterpreted functions for "simulated" CVM evidence and events. *)
Ltac do_assert_remote t e p i ac :=
  assert (
      build_cvm t
                      {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |} =
      (resultC tt,
       {| st_ev := cvm_evidence_core t p e;
          st_trace := cvm_events_core t p (get_et e);
          st_pl := p; 
          st_evid :=  (i + event_id_span t); 
          st_AM_config := ac
       |})
    ) by (eapply build_cvm_external).


(*
Ltac do_assume_remote t e p i (* x *) :=
  (* do_t_at_zero t x; *)
  do_assert_remote (*x*) t e p i (* ;
  do_assert_unannoPar t x *) .
 *)


(**  * Event ID spans same for a term and its corresponding core term. *)
Lemma event_id_spans_same : forall t,
    event_id_span' t = event_id_span (copland_compile t).
Proof.
  intros.
  induction t; ff.
  -
    destruct a; ff; try tauto.
    (* 
    +
      destruct s; ff.
  -
    jkjke'.
  -
    destruct s0; ff; lia.
  -
    destruct s0; ff; lia. *)
Qed.





(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t pt e tr p i e' tr' p' i' ac ac',
    term_to_coreP t pt ->
    build_cvmP
      pt
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i;
         st_AM_config := ac |}
      (resultC tt)
      {|
        st_ev := e';
        st_trace := tr';
        st_pl := p';
        st_evid := i';
        st_AM_config := ac'
      |} ->
    i' = i + event_id_span' t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    wrap_ccp_anno.

  -
    destruct a;
      try destruct a;
      ff; try tauto;
      wrap_ccp_anno; ff.
    + unfold do_asp' in *;
      destruct (do_asp (asp_paramsC a l p0 t) (get_bits e) p i ac); unfold failm, ret in *; 
      simpl in *; eauto; try congruence.
    + unfold do_asp' in *;
      destruct (do_asp (asp_paramsC a l p0 t) [] p i ac); unfold failm, ret in *; 
      simpl in *; eauto; try congruence.
    + unfold do_asp' in *;
      destruct (do_asp sig_params (get_bits e) p i ac); unfold failm, ret in *; 
      simpl in *; eauto; try congruence.
    + unfold do_asp' in *;
      destruct (do_asp hsh_params (get_bits e) p i ac); unfold failm, ret in *; 
      simpl in *; eauto; try congruence.
    + unfold do_asp' in *;
      destruct (do_asp (enc_params p0) (get_bits e) p i ac); unfold failm, ret in *; 
      simpl in *; eauto; try congruence.
  -
    lia.
  -
    wrap_ccp_anno.
    assert (st_evid0 = i + event_id_span' t1).
    inv H. simpl in *.
    eapply IHt1; eauto.
    2: { eassumption. }
    econstructor; eauto.

    assert (i' = st_evid0 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    lia.
  -
    destruct s0; destruct s1.
    +
      wrap_ccp_anno.

      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
  - (* bpar case *)
    destruct s0; destruct s1.
    +
      wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
      wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
            wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
      wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    
    lia.
Qed.


  
(** * CVM event ID span same as annotated term range *)
Lemma span_cvm: forall atp t annt i j e e' tr tr' p p' i' ac ac',
    build_cvmP
      atp
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i;
         st_AM_config := ac |} 
      (resultC tt)
      {| st_ev := e';
         st_trace := tr';
         st_pl := p';
         st_evid := i';
         st_AM_config := ac' |} ->
    
    term_to_coreP t atp -> 
    anno t i = (j, annt) ->
    j = i'.
Proof.
  intros.
  assert (j = i + event_id_span' t).
  {
    assert (j - i = event_id_span' t).
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


(** * Propositional version of span_cvm *)
Lemma anno_span_cvm: forall t pt annt i i' e e' p p' tr tr' st_evid1 ac ac',
    annoP_indexed annt t i i' ->
    term_to_coreP t pt ->
    build_cvmP pt
                     {|
                       st_ev := e ;
                       st_trace := tr ;
                       st_pl := p;
                       st_evid := i;
                       st_AM_config := ac
                     |} (resultC tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_pl := p';
                       st_evid := st_evid1;
                       st_AM_config := ac'
                     |} ->
    i' = st_evid1.
Proof.
  intros.
  invc H.
  eapply span_cvm; eauto.
Qed.





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





(** * Axiom:  assume parallel CVM threads preserve well-formedness of EvC bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

(** * Lemma:  CVM execution preserves well-formedness of EvC bundles 
      (Evidence Type of sufficient length for raw evidence). *)
Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p' i i' ac ac',
    wf_ec e ->
        build_cvmP t1
                    {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i;
                       st_AM_config := ac |}
                    (resultC tt)
                    {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i';
                       st_AM_config := ac' |} ->
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
    +
      destruct f.
      ++
        ff.
        econstructor.
        ff.
      ++
        ff.
        econstructor.
        ff.
      ++
        ff.
        econstructor.
        ff.
        (* 
        congruence. *)
      ++
        ff.
        econstructor.
        ff.
      ++
        ff.
        econstructor.
        ff.
        
        
  -
    wrap_ccp.

    eapply wf_ec_preserved_remote; eauto.

  -
    wrap_ccp.
    eauto.
  -
    wrap_ccp.

    (*

    do_wfec_split. *)

    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    econstructor.
    dd.
    inv_wfec.
    repeat jkjke'.
    eapply app_length.

  -
    wrap_ccp.

    (*
    
    do_wfec_split. *)

    find_apply_hyp_hyp.

      inv_wfec;
      ff;
      econstructor;
      dd;
      repeat jkjke'.

    erewrite app_length.

    assert (wf_ec (evc r1 e1)).
    {
      rewrite <- Heqe1.
      eapply wf_ec_preserved_par.
      econstructor; eassumption.
    }

    solve_by_inversion.
Qed.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [(*H: well_formed_r ?t, *)
          H2: wf_ec ?stev,
              H3: build_cvmP ?t
                                   {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |}
                                   (resultC tt)
                                   {| st_ev := ?stev'; st_trace := _; st_pl := _; st_evid := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [(*apply H |*) apply H2 | apply H3])
                                 
    end.


Axiom ev_cvm_mtc: forall ct p e loc,
    parallel_vm_thread loc ct p mt_evc = parallel_vm_thread loc (lseqc (aspc CLEAR) ct) p e.


(** * Lemma:  Evidence Type denotation respects evidence reference semantics  *)
Lemma cvm_ev_denote_evtype: forall annt p e,
    (*annoP annt t -> *)
    et_fun (cvm_evidence_denote annt p e) = (aeval annt p (et_fun e)).
Proof.
  intros.
  generalizeEverythingElse annt.
  induction annt; intros.
  -
    dd.
    destruct a; dd;
      try eauto.
    +
      destruct f; ff.
      destruct s; ff.
      destruct s; ff.
  -
    dd.
    eauto.
  -
    dd.
    assert (et_fun (cvm_evidence_denote annt1 p e) = aeval annt1 p (et_fun e)) by eauto.
    repeat jkjke.
  -
    dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
  -
    dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
Defined.


(** * Lemma:  CVM execution always succeeds *)
Lemma exists_some_cc: forall t st,
    exists st',
      build_cvm t st = (resultC tt, st').
Proof.
  intros.
  destruct (build_cvm t st) eqn:ee.
  do_asome.
  subst.
  eauto.
Defined.

Ltac do_exists_some_cc t st :=
    assert_new_proof_by
      (exists st', build_cvm t st = (resultC tt, st') )
      ltac:(eapply exists_some_cc);
    destruct_conjs.



(** * Helper Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. *)
Lemma st_trace_cumul'' : forall t m k e p v_full v_suffix o_suffix i ac,
    build_cvmP t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_evid := i;
                       st_AM_config := ac |}
               (resultC tt) v_full ->
    
    build_cvmP t
                     {| st_ev := e; st_trace := k; st_pl := p; st_evid := i;
                       st_AM_config := ac |}
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



(** * Instance of st_trace_cumul'' where k=[] *)
Lemma st_trace_cumul' : forall t m e p v_full v_suffix o_suffix i ac,
    build_cvmP t
               {| st_ev := e; st_trace := m; st_pl := p; st_evid := i; st_AM_config := ac |}
               (resultC tt) v_full ->
    
    build_cvmP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}
                     o_suffix v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  intros.
  eapply st_trace_cumul''; eauto.
  repeat rewrite app_nil_r.
  eauto.
Defined.


(** * Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. 
      TODO:  rename to st_trace_cumul 
*) 
Lemma suffix_prop : forall t e e' tr tr' p p' i i' ac ac',
    build_cvmP t
           {| st_ev := e;
              st_trace := tr;
              st_pl := p;
              st_evid := i; st_AM_config := ac |}
           (resultC tt)
           {|
             st_ev := e';
             st_trace := tr';
             st_pl := p';
             st_evid := i'; st_AM_config := ac' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}.
  wrap_ccp.
  (*

  rewrite ccp_iff_cc in *. *)

  repeat do_st_trace_assumps.
  repeat find_rw_in_goal.
  eexists.

  erewrite st_trace_cumul''.
  3: {
    eassumption.
  }
  simpl.
  tauto.
  rewrite app_nil_r.
  eassumption.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': build_cvmP ?t
         {| st_ev := _; st_trace := ?tr; st_pl := _; st_evid := _ |}
         (resultC tt)
         {| st_ev := _; st_trace := ?tr'; st_pl := _; st_evid := _ |}
         (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H'])
             name
  end.

(** * Structural Lemma:   Decomposes the CVM trace for the lseq phrase into the appending of the two traces
      computed by its subterms, where each subterm starts from the empty trace.

      Useful for leveraging induction hypotheses in the lseq case of induction that require empty traces in the 
      initial CVM state. *)
Lemma alseq_decomp : forall t1' t2' e e'' p p'' tr i i'' ac ac'',
    build_cvmP
      (lseqc t1' t2')
      {| st_ev := e;
         st_trace := [];
         st_pl := p;
         st_evid := i; st_AM_config := ac |}
      (resultC tt)
      {| st_ev := e'';
         st_trace := tr;
         st_pl := p'';
         st_evid := i''; st_AM_config := ac'' |} ->

    exists e' tr' p' i' ac',
      build_cvmP
        t1'
        {| st_ev := e;
           st_trace := [];
           st_pl := p;
           st_evid := i; st_AM_config := ac |}
        (resultC  tt)
        {| st_ev := e';
           st_trace := tr';
           st_pl := p';
           st_evid := i'; st_AM_config := ac' |} /\
      exists tr'',
        build_cvmP
          t2'
          {| st_ev := e';
             st_trace := [];
             st_pl := p';
             st_evid := i'; st_AM_config := ac' |}
          (resultC tt)
          {| st_ev := e'';
             st_trace := tr'';
             st_pl := p'';
             st_evid := i''; st_AM_config := ac'' |} /\
        tr = tr' ++ tr''.     
Proof.
  intros.
  wrap_ccp_dohi.
  
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.

  split.
  +
    eassumption.
  +
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_pl := st_pl0; st_evid := st_evid0; st_AM_config := st_AM_config0 |}.
    vmsts.

    eexists.

    wrap_ccp_dohi.

    split.
    ++
      eassumption.
    ++
      repeat do_st_trace.
      repeat find_rw_in_goal.
      eapply st_trace_cumul'; 
        eassumption.
Defined.


(** Structural convenience lemma:  reconfigures CVM execution to use an empty initial trace *)
Lemma restl : forall t e e' x tr p p' i i' ac ac',
    build_cvmP t
                     {| st_ev := e; st_trace := x; st_pl := p; st_evid := i; st_AM_config := ac|}
                     (resultC tt)
                     {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_evid := i'; st_AM_config := ac' |} ->

    build_cvmP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}
                     (resultC tt)
                     {| st_ev := e'; st_trace := tr; st_pl := p'; st_evid := i'; st_AM_config := ac' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac |}.
  wrap_ccp_dohi.

  assert (st_trace = tr).
  {
    do_st_trace.
    rewrite H0; clear H0.
    assert (tr = st_trace).
    {
      assert (Cvm_St.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config|} =
              x ++ Cvm_St.st_trace {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config |}).
      {
        eapply st_trace_cumul'; eauto.
      }
      simpl in *.
      eapply app_inv_head; eauto.
    }
    jkjke.
  }
  congruence.
Defined.

Ltac do_restl :=
  match goal with
  | [H: build_cvmP ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |}
        (resultC tt)
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'; st_evid := ?i'; st_AM_config := ?ac' |}
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by
      (build_cvmP t
                        {| st_ev := e; st_trace := []; st_pl := p; st_evid := i; st_AM_config := ac|}
                        (resultC tt)
                        {| st_ev := e'; st_trace := x; st_pl := p'; st_evid := i'; st_AM_config := ac' |})
      ltac:(eapply restl; [apply H])
  end.




(** * Lemma:  evidence semantics same for annotated and un-annotated terms *)
Lemma eval_aeval': forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros;
    repeat ff;
    repeat jkjke.
Defined.







(** * Lemma:  parallel CVM threads preserve the reference Evidence Type semantics (eval). *)
Lemma par_evidence_r: forall l p bits bits' et et' t2,
    parallel_vm_thread l (copland_compile t2) p (evc bits et) = evc bits' et' ->
    et' = eval t2 p et.
Proof.
  intros.
  rewrite par_evidence in H.
  rewrite <- at_evidence in H.
  rewrite <- remote_Evidence_Type_Axiom with (bits := bits).
  rewrite H.
  simpl.
  tauto.
Qed.
         
(** * Axiom about "simulated" parallel semantics of CVM execution:
      Executing a "CLEAR" before a term is the same as executing that term with mt initial evidence.
      TODO:  can we use existing axioms to prove this? *)
Axiom par_evidence_clear: forall l p bits et t2,
    parallel_vm_thread l (lseqc (aspc CLEAR) t2) p (evc bits et) =
    parallel_vm_thread l t2 p mt_evc.

(** * Main Lemma:  CVM execution maintains the Evidence Type reference semantics (eval) for 
      its internal evidence bundle. *)
Lemma cvm_refines_lts_evidence' : forall t tr tr' bits bits' et et' p p' i i' ac ac',
    build_cvmP (copland_compile t)
                     (mk_st (evc bits et) tr p i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') tr' p' i' ac') ->
    et' = (Term_Defs.eval t p et).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    subst.
    destruct a;
      (try dd; eauto).
    +
      destruct s; dd.
      destruct f; dd; eauto.
      unfold mt_evc in *.
      ff.
      destruct f; dd; eauto.
      unfold mt_evc in *.
      ff.
      unfold mt_evc in *.
      ff.

      

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    dd.
    erewrite <- remote_Evidence_Type_Axiom.
    jkjke.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eapply restl.
    eassumption.
    destruct_conjs.

    wrap_ccp.
    
    destruct x.
    repeat jkjke'.
    
  - (* abseq case *)

    (*
    do_suffix blah.
    do_suffix blah'. *)

    wrap_ccp.

    destruct s0; destruct s1; ff; 
      wrap_ccp;
      repeat find_apply_hyp_hyp; congruence.
      
   - (* abpar case *)

    (*
    do_suffix blah.
    do_suffix blah'. *)

    wrap_ccp.

    destruct s0; destruct s1; ff.

    +
      wrap_ccp.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p et).
      {
        eapply par_evidence_r.
        eassumption.
      }
      congruence.
      
    +
      wrap_ccp.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p mt).
      {
        rewrite par_evidence_clear in *.
        eapply par_evidence_r.
        eassumption.
      }
      
      congruence.
    +
      wrap_ccp.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p et).
      {
        eapply par_evidence_r.
        eassumption.
      }
      congruence.
    +
      wrap_ccp.
      find_apply_hyp_hyp.

      assert (e0 = eval t2 p mt).
      {
        rewrite par_evidence_clear in *.

        eapply par_evidence_r.
        eassumption.
      }
      congruence.
Qed.

(** * Propositional version of CVM Evidence Type preservation. *)
Lemma cvm_refines_lts_evidence :
  forall t t' tr tr' bits bits' et et' p p' i i' ac ac',
    term_to_coreP t t' ->
    build_cvmP t'
                     (mk_st (evc bits et) tr p i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') tr' p' i' ac') ->
    et' = (Term_Defs.eval t p et).
Proof.
  intros.
  invc H.
  eapply cvm_refines_lts_evidence'.
  eauto.
Qed.






(*
TODO: try this lemma again after getting appraisal Lemmas settled 
*)


(** * Lemma:  relating reconstructed CVM EvC bundles via the EvidenceC evidence denotation. *)
Lemma cvm_raw_evidence_denote_fact :
  forall t annt t' tr tr' bits bits' et et' p p' i i' ec ec' ac ac',
    build_cvmP t
                     (mk_st (evc bits et) tr p i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') tr' p' i' ac') ->
    term_to_coreP t' t ->
    annoP_indexed annt t' i i' ->

    reconstruct_evP (evc bits et) ec ->
    reconstruct_evP (evc bits' et') ec' ->

    cvm_evidence_denote annt p ec = ec'.
Proof.
  intros.
  generalizeEverythingElse t'.
  induction t'; intros.
  -
    wrap_ccp_anno.
    
    destruct a. (* wrap_ccp_anno. *)
    + (* NULL case *)
      wrap_ccp_anno.
      ff.
      invc H3.
      dd.
      tauto.   
    + (* CPY case *)
      wrap_ccp_anno.
      dd.
      eapply reconP_determ; eauto.

    + (* ASPC case *)
      wrap_ccp_anno.
      ff.
      ++ (* COMP case *)
        wrap_ccp_anno.
        invc H3.
        ff.
        assert (bits = encodeEv ec).
        {
          symmetry.
          invc H2.
          eapply recon_encodeEv.
          econstructor.
          eassumption.
        }
        subst.

        assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        eassumption.
      }
      congruence.
      ++ (* COMP NONE case *)
        wrap_ccp_anno.
        invc H3.
        ff.
      ++ (* ENCR ALL case *)
        wrap_ccp_anno.
        invc H3.
        ff.
         assert (bits = encodeEv ec).
        {
          symmetry.
          invc H2.
          eapply recon_encodeEv.
          econstructor.
          eassumption.
        }
        subst.

        assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        eassumption.
      }
      congruence.

      ++ (* ENCR NONE case *)
        wrap_ccp_anno.
        invc H3.
        ff.
        
      ++ (* EXTD ALL case *)
        wrap_ccp_anno.
        invc H3.
        ff.
        invc H2.
        ff.
        jkjke'.
        ff.
        assert (bits = encodeEv ec).
        {
          symmetry.
          eapply recon_encodeEv.
          econstructor.
          eassumption.
        }
        subst.
        tauto.
      ++ (* EXTD NONE case *)
        wrap_ccp_anno.
        invc H3.
        ff.
      ++ (* KILL ALL case *)
        wrap_ccp_anno.
        invc H3.
        ff.
      ++ (* KILL NONE case *)
        wrap_ccp_anno.
        invc H3.
        ff.
             
      ++
        wrap_ccp_anno.
        invc H3.
        ff.
        assert (et_fun ec' = et').
        {
          symmetry.
          eapply etfun_reconstruct.
          econstructor.
          
        eassumption.
        }
        invc H2.
        unfold reconstruct_ev in *.
        congruence.
      ++
        wrap_ccp_anno.
        invc H3.
        ff.

    +
      wrap_ccp.
      dd.
      invc H3; invc H2.
      dd.
      jkjke'.
      dd.
      (* Search (encodeEv _ = _). *)
      rewrite recon_encodeEv with (bits:=bits) (et:=et).
      tauto.
      econstructor; eassumption.

    +
      wrap_ccp.
      invc H3; invc H2.
      dd.
      assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        econstructor.
        eassumption.
      }

      rewrite recon_encodeEv  with (bits:=bits) (et:=et).
      congruence.
      econstructor; eassumption.
    +
      wrap_ccp.
      invc H3; invc H2.
      dd.
      assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        econstructor.
        eassumption.
      }

      rewrite recon_encodeEv  with (bits:=bits) (et:=et).
      congruence.
      econstructor; eassumption.
      

  -
    wrap_ccp_anno.
    ff.
    wrap_ccp_anno.

    do_assert_remote (copland_compile t') (evc bits et) p (S i) ac'.

    assert (evc bits' et' = cvm_evidence_core (copland_compile t') p (evc bits et)). {

      rewrite at_evidence in *.
      unfold cvm_evidence in *.
      rewrite H5.
      tauto.
    }

    eapply IHt'.
    econstructor.
    rewrite <- H7 in H4.
    eassumption.
    econstructor; eauto.
    assert (n = (S i + event_id_span (copland_compile t'))).
    {
      wrap_ccp_anno.
      eapply anno_span_cvm.
      eassumption.
      2: { eassumption. }
      econstructor; eauto.
    }
    subst.
    eassumption.
    eassumption.
    eassumption.

  - (* lseq case *)
    wrap_ccp_anno.
    ff.
    wrap_ccp_anno.
    ff.

    assert (n = st_evid0).
    {
      eapply anno_span_cvm.
      eassumption.
      2: { eassumption. }
      econstructor; eauto.
    }
    
    dd.

    destruct st_ev0.

    assert (wf_ec (evc bits et)).
    {
      eapply wfec_recon; eauto.
    }

    do_wfec_preserved.

    do_somerecons.
    
    assert ((cvm_evidence_denote a p ec) = H8).
    {
      eapply IHt'1.
      
      eassumption.
      econstructor; eauto.
      eassumption.

      eassumption.
      eassumption.
    }
    
    subst.
    eapply IHt'2.
    apply Heqp1.
    econstructor; eauto.
    eassumption.
    eauto.
    eauto.
    
  - (* bseq case *)
    wrap_ccp_anno;
      ff;
      wrap_ccp_anno.
    
    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.

      Print do_inv_recon.

      Print do_recon_inv.

      do_somerecons.

      (*
      assert (reconstruct_evP (evc r e4) e).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e5) e0).
    {
      econstructor.
      ff.
    } 
    *)

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      econstructor; eauto.
    }

    assert (cvm_evidence_denote a0 st_pl1 ec = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      eassumption.
      econstructor; eauto.
    } 
    dd.
    congruence.
    +
            do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      (*
      assert (reconstruct_evP (evc r e4) e).
      {
        econstructor.
        ff.
      }

    assert (reconstruct_evP (evc r0 e5) e0).
    {
      econstructor.
      ff.
    }
    *)
    do_somerecons.

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      econstructor; eauto.
    }

    assert (cvm_evidence_denote a0 st_pl1 mtc = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor. ff.
      econstructor; eauto.
    }
    
    dd.
    congruence.

    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.

      do_somerecons.

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp8. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 mtc = e1).
    {
      eapply IHt'1.
      apply Heqp8.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      econstructor; eauto.
    }

     assert (cvm_evidence_denote a0 st_pl1 ec = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor. ff.
      econstructor; eauto.
    }

    dd.
    congruence.
    


    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

    do_somerecons.

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid1).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp9. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl1 mtc = e1).
    {
      eapply IHt'1.
      apply Heqp9.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      econstructor; eauto.
    }

     assert (cvm_evidence_denote a0 st_pl1 mtc = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor. ff.
      econstructor; eauto.
    }
    dd.
    congruence.



  - (* bpar case *)
    wrap_ccp_anno;
      ff;
      wrap_ccp_anno.
    
    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      do_somerecons.

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      econstructor; eauto.
    }

    do_assert_remote (copland_compile t'2) (evc bits et) p (st_evid) ac'.

    wrap_ccp_anno.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    find_rewrite.

    assert (cvm_evidence_denote a0 p ec = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        apply Heqp1.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      eassumption.
      econstructor; eauto.
    }
        
    dd.
    congruence.


    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      do_somerecons.

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp2. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p ec = e1).
    {
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      eassumption.
      econstructor; eauto.
    }

     do_assert_remote (copland_compile t'2) mt_evc p (st_evid) ac'.

    wrap_ccp_anno.

    rewrite <- ev_cvm_mtc in *.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    find_rewrite.


     assert (cvm_evidence_denote a0 p mtc = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor; eauto.
      econstructor; eauto.
    }
    
      
    dd.
    congruence.


    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      do_somerecons.

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp3. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p mtc = e1).
    {
      eapply IHt'1.
      eassumption.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      econstructor; eauto.
    }

     do_assert_remote (copland_compile t'2) (evc bits et) p (st_evid) ac'.

    wrap_ccp_anno.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    find_rewrite.

     assert (cvm_evidence_denote a0 p ec = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      eassumption.
      econstructor; eauto.
    }
    
      
    dd.
    congruence.

    +
      do_rewrap_reconP.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      assert (wf_ec mt_evc).
      {
        econstructor.
        ff.
      }

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.
      

      do_somerecons.

    assert (i + 1 = S i) as H13 by lia.
    rewrite H13 in *; clear H13.

    assert (n = st_evid).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { 
             apply Heqp3. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a p mtc = e1).
    {
      eapply IHt'1.
      apply Heqp3.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      econstructor; eauto.
    }

     do_assert_remote (copland_compile t'2) mt_evc p (st_evid) ac'.

    wrap_ccp_anno.

    rewrite <- ev_cvm_mtc in *.

    rewrite par_evidence in *.

    unfold cvm_evidence in *.
    find_rewrite.


     assert (cvm_evidence_denote a0 p mtc = e2).
    {
      eapply IHt'2.
      eassumption.
      econstructor; eauto.
      assert (n0 = st_evid + event_id_span (copland_compile t'2)).
      {
        eapply anno_span_cvm.
        eassumption.
        2: { eassumption. }
   
        econstructor; eauto.
      }
      dd.

      eassumption.
      econstructor; eauto.
      econstructor; eauto.
    }
    
      
    dd.
    congruence.
Qed.


Lemma cvm_raw_evidence_denote_fact_eval :
  forall t annt t' tr tr' bits bits' et et' p p' i i' ec ec' ac ac',
    build_cvmP t
                     (mk_st (evc bits et) tr p i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') tr' p' i' ac') ->
    term_to_coreP t' t ->
    annoP_indexed annt t' i i' ->

    reconstruct_evP (evc bits et) ec ->
    reconstruct_evP (evc bits' (eval t' p et)) ec' ->

    cvm_evidence_denote annt p ec = ec'.
Proof.
  intros.
  assert (et' = eval t' p et).
  {
    eapply cvm_refines_lts_evidence.
    eassumption.
    eassumption.
  }
  eapply cvm_raw_evidence_denote_fact; eauto.
  congruence.
Qed.
  




































(** BEGIN Deprecated parallel annotated term stuff *)

(*
Lemma anno_parP_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parP pt t.
Proof.
  intros.
  econstructor.
  eexists.
  jkjke.
Defined.

(*
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par t loc = (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.
 *)
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.

 *)

(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.
 *)


(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = Some (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.



Ltac inv_annoparP :=
  match goal with
  | [H: anno_parP _ _ (* ?t (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Ltac inv_annoparPloc :=
  match goal with
  | [H: anno_parPloc _ _ _(*?t (?c _) _ *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.
 *)


(*
Ltac wrap_annopar :=
  inv_annoparP;
  dd;
  repeat do_annopar_redo.

Ltac wrap_annoparloc :=
  inv_annoparPloc;
  dd;
  repeat do_annopar_loc_redo.
 *)


(** END Deprecated parallel annotated term stuff *)
