Require Import ErrorStMonad_Coq BS Maps Term_Defs_Core Term_Defs Cvm_Run Cvm_St.

Require Import ErrorStringConstants.

Require Export AM_St.

Require Import List.
Import ListNotations.

Definition fromSome{A E:Type} (default:A) (opt:ResultT A E): A :=
  match opt with
  | resultC x => x
  | _ => default
  end.

Definition run_am_app_comp{A:Type} (am_comp:AM A) (default_A:A) : A :=
  let optRes := evalErr am_comp empty_amst in
  fromSome default_A optRes.

Definition am_newNonce (bs:BS) : AM nat :=
  oldSt <- get ;;
  let oldMap := am_nonceMap oldSt in
  let oldId := am_nonceId oldSt in
  let newMap := map_set oldMap oldId bs in
  let newId := oldId + 1 in
  put (mkAM_St newMap newId) ;;
  ret oldId.

Definition am_getNonce (nid:nat) : AM BS :=
  oldSt <- get ;;
  let oldMap := am_nonceMap oldSt in
  let resopt := map_get oldMap nid in
  match resopt with
  | Some res => ret res
  | None => failm (am_error errStr_amNonce)
  end.


Definition am_runCvm_nonce (t:Term) (p:Plc) (bs:BS) (ac : AM_Config) : AM (nat * RawEv) :=
  nid <- am_newNonce bs ;;
  ret (nid, run_cvm_rawEv t p [bs] ac).
