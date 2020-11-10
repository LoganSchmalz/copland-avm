Require Import Term ConcreteEvidence GenStMonad MonadVM MonadAM.


Fixpoint build_app_comp (t:AnnoTerm) (p:Plc) : AM (VM (EvidenceC -> EvidenceC)) :=
  match t with
  | alseq (n,n') t' (aasp r' SIG) =>
    app_id <- am_get_sig_asp p ;;
    d <- build_app_comp t' p ;;
    let c :=
        (
          e <- get_ev ;;
          pr <- extractSig e ;;
          let '(bs,e') := pr in
          res <- checkSig n app_id e' bs ;;
          put_ev e' ;;
          e_res <- d ;;
          ret (fun x => ggc res (e_res x))) in
    ret c   

  | alseq (n,n') t1 t2 =>
    c <- build_app_comp t1 p ;;
    d <- build_app_comp t2 p ;;
    let cc :=
        (
          g <- d ;;
          f <- c ;;
          ret (fun x => g (f x))
        ) in
    ret cc

        
  | aasp (n,n') (ASPC i args) =>
    app_id <- am_get_app_asp p i ;;
    let c :=
        (
          e <- get_ev ;;
          pr <- extractUev e ;;
          let '(bs,e') := pr in
          res <- checkUSM n app_id args bs ;;
          put_ev e' ;;
          ret (fun x => (uuc n res x) )) in
    ret c

  | aasp (n,n') (SIG) =>
    app_id <- am_get_sig_asp p ;;
    let c :=
        e <- get_ev ;;
        pr <- extractSig e ;;
        let '(bs,e') := pr in
        res <- checkSig n app_id e' bs ;;
        put_ev e' ;;
        ret (fun x => ggc res x) in
    
    ret c

  | aasp (n,n') (CPY) =>
    let c :=
        ret (fun x => x) in    
    ret c
        
  (*
  | aasp (n,n') (HSH) =>
   (* app_id <- am_get_sig_asp p ;; *) (* TODO: get_hsh_asp impl *) 
    let c :=
        e <- get_ev ;;
        pr <- extractHsh e ;;
        let '(bs,e') := pr in
        (*
        res <- checkSig n app_id ([encodeEv e'] ++ [bs] (* ++ args*) ) ;;
        put_ev e' ;; (* TODO: does this have any effect? *) 
        ret (ggc res e') *)
        put_ev e' ;;
        ret (fun x => hhc 0 x) in
        
    ret c     
   *)
        
  | aatt r q t' =>
    build_app_comp t' q
(*| _ => ret (ret (fun _ => mtc)) *)
  end.

(*
  e <- get_ev ;;
  pr <- extractComp e ;;
  let '(e1,e2) := pr in
  put_ev e1 ;;
  e1_res <- c ;;
  put_ev e2 ;;
  e2_res <- d ;;
  ret (ssc e1_res e2_res)
 *)
