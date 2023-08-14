Require Import Term_Defs Manifest ErrorStMonad_Coq (* AM_Monad Impl_appraisal *) .

Definition JsonT : Set. Admitted.

Definition default_Json: JsonT.
Admitted.

Definition strToJson (s:StringT): ResultT JsonT DispatcherErrors.
Admitted.

Definition jsonToStr (js:JsonT): StringT.
Admitted.

Definition requestToJson (req:CvmRequestMessage): JsonT.
Admitted.

Definition responseToJson (resp:CvmResponseMessage): JsonT.
Admitted.

Definition amRequestToJson (req:AM_RequestMessage): JsonT.
Admitted.

Definition appResponseToJson (resp:AppraisalResponseMessage): JsonT.
Admitted.

Definition jsonToRequest (j:JsonT) : ResultT CvmRequestMessage DispatcherErrors.
Admitted.

Definition jsonToResponse (j:JsonT) : ResultT CvmResponseMessage DispatcherErrors.
Admitted.

Definition jsonToAmRequest (j:JsonT): AM_RequestMessage.
Admitted.