Require Import ConcreteEvidence AutoApp Auto Helpers_CvmSemantics Term_Defs Anno_Term_Defs Cvm_St Cvm_Impl Defs StructTactics OptMonad_Coq IO_Stubs Evidence_Bundlers Axioms_Io External_Facts.

Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics PeanoNat.


Require Import Cvm_Monad.



(*

(* This function is for verification purpuses only.  In extracted code, it will likely
     act like an identity function
     (i.e. ignore the non-computationally-relevant params). *)
Definition do_asp_denote_bs (ps:ASP_PARAMS) (ev:RawEv) (p:Plc) (x:Event_ID): BS.
Admitted. (* TODO:  fill this in with some sort of callback + default value? *)

*)

Definition cvm_evidence_denote_asp (a:ASP) (p:Plc) (e:EvidenceC) (x:Event_ID): EvidenceC :=
  match a with
  | NULL => mtc
  | CPY => e
  | ASPC sp fwd params =>
    match fwd with
    | COMP => hhc p params
                 (do_asp_denote_bs params (encodeEv (spc_ev sp e)) p x)
                 (sp_ev sp (et_fun e))
    | EXTD => ggc p params
                 (do_asp_denote_bs params (encodeEv (spc_ev sp e)) p x)
                 (spc_ev sp e)
    | ENCR => eec p params
                 (do_asp_denote_bs params (encodeEv (spc_ev sp e)) p x)
                 (sp_ev sp (et_fun e))
    | KEEP => (spc_ev sp e)
    | KILL => mtc (* kkc p params (sp_ev sp (et_fun e)) *)
    end
  | SIG => ggc p sig_params
              (do_asp_denote_bs sig_params (encodeEv e) p x)
              e
  | HSH => hhc p hsh_params
              (do_asp_denote_bs hsh_params (encodeEv e) p x)
              (et_fun e)
  | ENC q => eec p (enc_params q)
                (do_asp_denote_bs (enc_params q) (encodeEv e) p x)
                (et_fun e)
  end.


(** * Denotation function of a Typed Concrete Evidence value from an annotated term, initial place, initial evidence *)
Fixpoint cvm_evidence_denote (t:AnnoTerm) (p:Plc) (ec:EvidenceC) : EvidenceC :=
  match t with
  | aasp (i,_) x => cvm_evidence_denote_asp x p ec i
  | aatt _ q x => cvm_evidence_denote x q ec
  | alseq _ t1 t2 => cvm_evidence_denote t2 p (cvm_evidence_denote t1 p ec)
  | abseq _ s t1 t2 => ssc (cvm_evidence_denote t1 p ((splitEvl s ec)))
                         (cvm_evidence_denote t2 p ((splitEvr s ec)))
  | abpar _ s t1 t2 => ssc (cvm_evidence_denote t1 p ((splitEvl s ec)))
                         (cvm_evidence_denote t2 p ((splitEvr s ec)))
  end.




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





(*
TODO: try this lemma again after getting appraisal Lemmas settled 
*)

Axiom cvm_evidence_core_at : forall t p bits bits' et ac,
  do_remote t p (evc bits et) ac = resultC bits' -> 
  cvm_evidence_core (copland_compile t) p (evc bits et) = evc bits' (eval t p et).


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

      assert (et_fun ec = et).
      {
        symmetry.
        eapply etfun_reconstruct.
        eassumption.


      }
      subst.
      eauto.

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
      ff.
      (* congruence. *)

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
        ff.
        (* tauto. *)
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
      Auto.ff.
      jkjke'.
      dd.
      (* Search (encodeEv _ = _). *)
      rewrite recon_encodeEv with (bits:=bits) (et:=et).
      unfold OptMonad_Coq.bind in *.
      ff.
      unfold OptMonad_Coq.bind in *.
      ff.

      econstructor; eauto.

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
      ff.
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
      ff.
      econstructor; eauto.
      

  - (* at case *)
    wrap_ccp_anno.
    repeat ff.
    wrap_ccp_anno.
    repeat ff.

    do_assert_remote (copland_compile t') (evc bits et) p (S i) ac'.

    
    assert (evc bits' (eval t' p et) = cvm_evidence_core (copland_compile t') p (evc bits et)). {

    symmetry.

    eapply cvm_evidence_core_at.
    eauto.

    (*
    Axiom cvm_evidence_correct_type : forall t p e e',
  cvm_evidence t p e = e' -> 
  get_et e' = eval t p (get_et e).
    *)

    (*
      rewrite at_evidence in *.
      unfold cvm_evidence in *.
      rewrite H5.
      tauto.  *)
    }

    eapply IHt'.
    econstructor.
    
    rewrite <- H5 in H4.
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
    
    assert ((cvm_evidence_denote a p' ec) = H9).
    {
      eapply IHt'1.
      
      apply Heqp0.
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
    Auto.ff.
    invc H2; invc H3.
    Auto.ff.
    try rewrite fold_recev in *.
    repeat Auto.ff.
    unfold OptMonad_Coq.bind in *.
    Auto.ff.

    try rewrite fold_recev in *.
    repeat do_wrap_reconP.
    Auto.ff.
      Auto.ff.
      unfold OptMonad_Coq.bind in *.
      Auto.ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
        econstructor; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.

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

    assert (cvm_evidence_denote a st_pl0 ec = e1).
    {
      repeat do_wrap_reconP.
      try rewrite fold_recev in *.
      repeat do_wrap_reconP.
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

    assert (cvm_evidence_denote a0 st_pl0 ec = e2).
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
      econstructor; eauto.
      eassumption.
    } 
    dd.
    congruence.


    +
    Auto.ff.
    invc H2; invc H3.
    Auto.ff.
    try rewrite fold_recev in *.
    repeat Auto.ff.
    unfold OptMonad_Coq.bind in *.
    Auto.ff.

    try rewrite fold_recev in *.
    repeat do_wrap_reconP.
    Auto.ff.
      Auto.ff.
      unfold OptMonad_Coq.bind in *.
      Auto.ff.

      assert (wf_ec (evc bits et)).
      {
        eapply wfec_recon; eauto.
        econstructor; eauto.
      }

      do_wfec_preserved.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.

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

    assert (cvm_evidence_denote a st_pl0 ec = e1).
    {
      repeat do_wrap_reconP.
      try rewrite fold_recev in *.
      repeat do_wrap_reconP.
      eapply IHt'1.
      apply Heqp2.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

    assert (wf_ec mt_evc).
    {
      econstructor.
      ff.
    }

    assert (cvm_evidence_denote a0 st_pl0 mtc = e2).
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
      econstructor; eauto.
      invc H11.
      eassumption.
    } 
    dd.
    congruence.



    +
    Auto.ff.
    invc H2; invc H3.
    Auto.ff.
    try rewrite fold_recev in *.
    repeat Auto.ff.
    unfold OptMonad_Coq.bind in *.
    Auto.ff.

    try rewrite fold_recev in *.
    repeat do_wrap_reconP.

      assert (wf_ec mt_evc).
      {
        econstructor.
        eauto.
      }



      do_wfec_preserved.
      repeat do_wrap_reconP.

      Print do_wfec_firstn.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.

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
             apply Heqp8. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl0 mtc = e1).
    {
      repeat do_wrap_reconP.
      try rewrite fold_recev in *.
      repeat do_wrap_reconP.
      eapply IHt'1.
      apply Heqp8.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

    assert (wf_ec mt_evc).
    {
      econstructor.
      ff.
    }

    assert (cvm_evidence_denote a0 st_pl0 ec = e2).
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
      econstructor; eauto.
      invc H11.
      eassumption.
    } 
    dd.
    congruence.

    +
    Auto.ff.
    invc H2; invc H3.
    Auto.ff.
    try rewrite fold_recev in *.
    repeat Auto.ff.
    unfold OptMonad_Coq.bind in *.
    Auto.ff.

    try rewrite fold_recev in *.
    repeat do_wrap_reconP.

      assert (wf_ec mt_evc).
      {
        econstructor.
        eauto.
      }



      do_wfec_preserved.
      repeat do_wrap_reconP.

      Print do_wfec_firstn.

      do_wfec_firstn.
      do_wfec_skipn.

      clear_skipn_firstn.

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
             apply Heqp9. }
   
        econstructor; eauto.
      }
      dd.

    assert (cvm_evidence_denote a st_pl0 mtc = e1).
    {
      repeat do_wrap_reconP.
      try rewrite fold_recev in *.
      repeat do_wrap_reconP.
      eapply IHt'1.
      apply Heqp9.
      econstructor; eauto.
      

      eassumption.
      econstructor; eauto.
      eassumption.
    }

    assert (wf_ec mt_evc).
    {
      econstructor.
      ff.
    }

    assert (cvm_evidence_denote a0 st_pl0 mtc = e2).
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
      econstructor; eauto.
      invc H11.
      eassumption.
    } 
    dd.
    congruence.

  - (* bpar case *)
    wrap_ccp_anno;
      Auto.ff;
      wrap_ccp_anno; 
      Auto.ff.
    
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




















  