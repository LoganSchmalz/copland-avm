Require Import Term Example_Phrases_Demo Cvm_Run.

Require Import Impl_appraisal Appraisal_IO_Stubs IO_Stubs AM_Monad StMonad_Coq.

Require Import List.
Import ListNotations.

Definition gen_nonce_if_none (initEv:option EvC) : AM EvC :=
  match initEv with
      | Some (evc ebits et) => ret (evc ebits et)
      | None =>
        let nonce_bits := gen_nonce_bits in
        nid <- am_newNonce nonce_bits ;;
        ret (evc [nonce_bits] (nn nid))
  end.

Definition gen_authEvC_if_some (ot:option Term) (pFrom:Plc) : AM EvC :=
  match ot with
  | Some auth_phrase =>
    let auth_rawev := run_cvm_rawEv auth_phrase pFrom [] in
    let auth_et := eval auth_phrase pFrom mt in
    ret (evc auth_rawev auth_et)
  | None => ret (evc [] mt)
  end.
  

Definition am_sendReq_gen (t:Term) (pFrom:Plc) (pTo:Plc)
           (initEv:option EvC) (authPhrase:option Term) : AM AppResultC :=
  evcIn <- gen_nonce_if_none initEv ;;
  auth_evc <- gen_authEvC_if_some authPhrase pFrom  ;;
  let '(evc init_ev init_et) := evcIn in
  let resev := am_sendReq t pFrom pTo auth_evc init_ev in
  let expected_et := eval t pTo init_et in
  gen_appraise_AM expected_et resev.


Definition am_sendReq_nonce (t:Term) (pFrom:Plc) (pTo:Plc) : AM AppResultC :=
  am_sendReq_gen t pFrom pTo None None.

Definition am_sendReq_nonce_auth (t:Term) (pFrom:Plc) (pTo:Plc) : AM AppResultC :=
  let auth_phrase := (* kim_meas *) ssl_sig in
  am_sendReq_gen t pFrom pTo None (Some auth_phrase).
  
Definition am_sendReq_auth (t:Term) (pFrom:Plc) (pTo:Plc) (initEv:RawEv) : AM AppResultC :=
  let auth_phrase := (* kim_meas *) ssl_sig in
  let initEv_et := mt in (* TODO:  make this a param? *)
  am_sendReq_gen t pFrom pTo (Some (evc initEv initEv_et)) (Some auth_phrase).

  
    

