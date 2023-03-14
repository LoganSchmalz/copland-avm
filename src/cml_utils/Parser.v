Require Import String Ascii List Nat Bool.
Require Import EqClass.
Require Import Lia.
Open Scope string_scope.

(* TODO: Add CharExtra! *)
Module CharExtra.
  Definition isDigit : ascii -> bool. Admitted.

  Definition isOctal : ascii -> bool. Admitted.

  Definition isHex : ascii -> bool. Admitted.

  Definition isLower : ascii -> bool. Admitted.

  Definition isUpper : ascii -> bool. Admitted.

  Definition isAlpha : ascii -> bool. Admitted.

  Definition isAlphaNum : ascii -> bool. Admitted.

  Definition isSpace : ascii -> bool. Admitted.

End CharExtra.

Inductive res (A B : Type) :=
| Ok : A -> res A B
| Err : B -> res A B.
Arguments Ok {A} {B}.
Arguments Err {A} {B}.

Definition nat_to_string : nat -> string. Admitted.

Definition cml_unit : Type. Admitted.
Definition unit_val : cml_unit. Admitted.

Global Instance eqclass_ascii : EqClass ascii := {
  eqb := Ascii.eqb;
  eqb_leibniz := Ascii.eqb_eq
}.

Global Instance eqclass_string : EqClass string := {
  eqb := String.eqb;
  eqb_leibniz := String.eqb_eq
}.

Module Type Parser.
  Import CharExtra.

  Definition stream (A : Type) : Type := (list A * nat * nat).

  Definition parser (A B : Type) `{HA : EqClass A} `{HB : EqClass B} : Type := 
    (stream B) -> ((res A string) * list B * nat * nat).
  
  Inductive consuming_parser {A B : Type} `{HA : EqClass A} `{HB : EqClass B} (p : parser A B) := {
    consuming_always : (forall cs line col cs' line' col' result,
      p (cs, line, col) = (Ok result, cs', line', col') ->
      List.length cs' < List.length cs \/ cs' = nil)
  }.
  (* Definition ParseClass {A B : Type} `{HA : EqClass A} `{HB : EqClass B} := (fun p => (@consuming_parser A B HA HB p)). *)

  (* parse: parser A ascii -> string -> res A string
     * `parse p str`
     * Runs the parser `p` over the string `str`.
     *)
  Definition parse {A : Type} `{HA : EqClass A} (p : (parser A ascii)) `{consuming_parser p} (str : string) : (res A string) :=
    match (p (String.list_ascii_of_string str , 1, 1)) with
    | (Ok x, _, _ , _) => Ok x
    | (Err msg, _, line, col) => 
        Err ("Error on line " ++ nat_to_string line ++ ", column " ++ nat_to_string col ++ ": " ++ msg)
    end.

  (* bind: parser A B -> (A -> parser C B) -> (stream B) -> parser C B
    * `bind p funcp`
    * Runs the parser `p` and upon success, applies `funcp` to the result and
    * continue to parse.
    *)
  Definition bind {A B C : Type} `{EqClass A} `{EqClass B} `{EqClass C} 
      (p : parser A B) (funcp : (A -> (parser C B))) (CP : consuming_parser p) (FuncCP : forall a : A, consuming_parser (funcp a)): (parser C B) :=
    fun (stream : stream B) =>
      match (p stream) with
      | (Ok x, cs', line', col') => funcp x (cs', line', col')
      | (Err msg, cs', line', col') => ((Err msg), cs', line', col')
      end.

  Ltac inv H := inversion H; subst; clear H.

  Create HintDb CP_db.

  Ltac cp_solver :=
    intros; econstructor; intros; cbv in *;
    repeat (
      eauto with CP_db; cbv in *;
      match goal with
      | H : context [ ?p (?cs, ?line, ?col) ] |- _ => 
        cbv in *;
        destruct (p (cs, line, col)) as [[[r lcs] ln] cl] eqn:E; destruct r; subst
      | CP : consuming_parser ?p, E : ?p _ = _ |- _ => 
        let CP' := fresh "CP" in
        destruct CP as [CP']; cbv in *;
        try rewrite E in *; pose proof (CP' _ _ _ _ _ _ _ E)
      | F : (_, _, _, _) = (_, _, _, _) |- _ => inv F
      end; try lia
    ).

  Lemma consuming_parser_bind : forall {A B C : Type} `{HA : EqClass A, HB : EqClass B, HC : EqClass C} 
      (p : parser A B) {CP : consuming_parser p} (funcp : (A -> (parser C B))) {FuncCP : forall a : A, consuming_parser (funcp a)},
    consuming_parser (bind p funcp CP FuncCP).
  Proof.
    intros. 
    econstructor; intros.
    destruct CP. cbv in H. destruct (p (cs, line, col)) eqn:E, p0, p0, r.
    - destruct (FuncCP a). 
      pose proof (consuming_always1 _ _ _ _ _ _ _ H). 
      pose proof (consuming_always0 _ _ _ _ _ _ _ E). destruct H0, H1; subst; cbv in *; try lia. right. eauto.
    - congruence.
  Qed.

  Hint Resolve consuming_parser_bind : CP_db.

  (* bindResult: (A -> res B string) -> (parser A C) -> (parser B C)
    * `bindResult func p`
    * Runs the parser `p` and upon success, applies `func` to the result.
    *)
  Definition bindResult {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (func : A -> res B string) (p : parser A C) (CP : consuming_parser p) : (parser B C) :=
    fun (stream : (stream C)) =>
      match p stream with
      | (Ok x, cs', line', col') => (func x, cs', line', col')
      | (Err err, cs', line', col') => (Err err, cs', line', col')
      end.

  Lemma consuming_parser_bindResult : forall {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (func : A -> res B string) (p : parser A C) (CP : consuming_parser p),
    consuming_parser (bindResult func p CP).
  Proof.
    cp_solver.
  Qed.

  Hint Resolve consuming_parser_bindResult : CP_db.

  (* map: (A -> B) -> parser A C -> parser B C
    * `map func p`
    * returns parser `p` and upon success, applies `func` to the result.
    *)
  Definition map {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (func : A -> B) (p : parser A C) (CP : consuming_parser p) : (parser B C) :=
    fun (stream : stream C) =>
      match p stream with
      | (Ok x, cs', line', col') =>
          (Ok (func x), cs', line', col')
      | (Err err, cs', line', col') =>
          (Err err, cs', line', col')
      end.

  Lemma consuming_parser_map : forall {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (func : A -> B) (p : parser A C) (CP : consuming_parser p),
    consuming_parser (map func p CP).
  Proof.
    cp_solver.
  Qed.

  Hint Resolve consuming_parser_map : CP_db.

  (** Getting rid of the pure parser, it is never used, and it breaks our Theorem about 
      parsers always consuming on success
        (* pure: 'a -> ('a, 'b) parser
          * `pure x`
          * A simple parser that successfully returns `x` without consuming any
          * input.
          *)
        Definition pure {A B : Type} `{EqClass A, EqClass B}
            (x : A) : (parser A B) :=
          fun (stream : stream B) => 
            match stream with
            | (cs, line, col) => (Ok x, cs, line, col)
            end.
  *)
  
  (* TODO: This is a type breaking thing! *)
  (* fail: string -> parser A string
    * `fail err`
    * A simple parser that fails, returning `err`, without consuming any input.
    *)
  Definition fail {A : Type} `{EqClass A}
      (err : string) : (parser A string) :=
    fun (stream : stream _) =>
      match stream with
      | (cs, line, col) => (Err err, cs, line, col)
      end.

  Lemma consuming_parser_fail : forall {A : Type} `{HA : EqClass A} (err : string),
    consuming_parser (fail err).
  Proof.
    cp_solver.
  Qed.

  Hint Resolve consuming_parser_fail : CP_db.

  (* eof: parser unit string
    * `eof`
    * A simple parser that succeeds exactly when there is no more input.
    *)
  Definition eof :=
    fun (stream : stream string) =>
      match stream with
      | (cs, line, col) =>
        match cs with
        | nil => (Ok unit_val, cs, line, col)
        | c::cs' => (Err "End of stream expected.", c::cs', line, col)
        end
      end.

  Lemma consuming_parser_eof : forall `{EqClass cml_unit},
    consuming_parser eof.
  Proof.
    econstructor; intros; cbv in *; destruct cs.
    - inv H0. eauto.
    - cp_solver.
  Qed.

  Hint Resolve consuming_parser_eof : CP_db.
  
  (* seq: parser A B -> parser C B -> parser C B
    * `seq p1 p2`
    * Runs parser `p1` and then, upon success, runs parser `p2`, discarding the
    * previous results.
    *)
  Definition seq {A B C: Type} `{EqClass A, EqClass B, EqClass C}
      (p1 : parser A B) (p2 : parser C B) (CP1 : consuming_parser p1) (CP2 : consuming_parser p2) : (parser C B) :=
    fun (s : stream B) => 
      bind p1 (fun _ => p2) CP1 (fun _ => CP2) s.

  Lemma consuming_parser_seq : forall {A B C: Type} `{EqClass A, EqClass B, EqClass C}
      (p1 : parser A B) (p2 : parser C B) (CP1 : consuming_parser p1) (CP2 : consuming_parser p2),
    consuming_parser (seq p1 p2 CP1 CP2).
  Proof.
    econstructor; intros. 
    pose proof (@consuming_parser_bind _ _ _ _ _ _ p1 CP1 (fun _ => p2) (fun _ => CP2)).
    inv H3.
    cbv in H2. pose proof (consuming_always0 cs line col cs' line' col').
    eapply H3. cbv. eauto.
  Qed.

  Hint Resolve consuming_parser_seq : CP_db.

  (* satisfy: (char -> bool) -> (char, char) parser
    * `satisfy pred`
    * A simple parser that succeeds exactly when `pred` returns true on the
    * next element in the stream. Does not consume input upon failure.
    *)
  Example newline := "010"%char.
  Definition satisfy (pred : ascii -> bool) : (parser ascii ascii) :=
    fun (s : stream ascii) =>
      match s with
      | (cs, line, col) =>
        match cs with
        | nil => (Err "End of stream reached too early.", nil, line, col)
        | c::cs' =>
            if pred c
            then if (c =? newline)%char
                then (Ok c, cs', 1 + line, 1)
                else (Ok c, cs', line, 1 + col)
            else (Err "Failed to satisfy a predicate.", cs, line, col)
        end
      end.

  Lemma consuming_parser_satisfy : forall pred,
    consuming_parser (satisfy pred).
  Proof.
    econstructor; intros.
    cbv in H. destruct cs eqn:CS.
    - inv H.
    - destruct (pred a).
      * destruct (match a with
          | Ascii a0 a1 a2 a3 a4 a5 a6 a7 =>
              if
              if
                if
                if
                  if
                  if if if a0 then false else true then if a1 then true else false else false
                  then if a2 then false else true
                  else false
                  then if a3 then true else false
                  else false
                then if a4 then false else true
                else false
                then if a5 then false else true
                else false
              then if a6 then false else true
              else false
              then if a7 then false else true
              else false
          end); inv H; cbv; lia.
      * inv H.
  Qed.
  
  Hint Resolve consuming_parser_satisfy : CP_db.

    (* label: string -> ('a, 'b) parser -> ('a, 'b) parser
    * `label errMsg p`
    * Runs parser `p` and if it fails without consuming input, then the error
    * message is replaced by `errMsg`.
    *)
  Definition label {A B : Type} `{EqClass A, EqClass B}
      (errMsg : string) (p : parser A B) (CP : consuming_parser p) : (parser A B) :=
    fun (s : stream _) =>
      match s with
      | (cs, line, col) =>
        match p (cs, line, col) with
        | (Err str, cs', line', col') =>
            if (andb (eqb line line') (andb (eqb col col') (eqb cs cs')))
            then (Err errMsg, cs, line, col)
            else (Err str, cs', line', col')
        | (Ok x, cs', line', col') => (Ok x, cs', line', col')
        end
      end.

  Lemma consuming_parser_label : forall {A B : Type} `{EqClass A, EqClass B}
      (errMsg : string) (p : parser A B) (CP : consuming_parser p),
    consuming_parser (label errMsg p CP).
  Proof.
    econstructor; intros.
    inv H1.
    destruct (p (cs, line, col)) eqn:PC, p0, p0, r.
    - destruct CP. pose proof (consuming_always0 _ _ _ _ _ _ _ PC); inv H3; eauto.
    - destruct ((line =? n0)%nat && ((col =? n)%nat && general_list_eq_class_eqb cs l)); inv H3.
  Qed.

  Hint Resolve consuming_parser_label : CP_db.

  (* parser_return: 'a -> ('b, 'c) parser -> ('a, 'c) parser
    * `parser_return x p`
    * Runs parser `p` and if it succeeds replace the result with `x`.
    *)
  Definition parser_return {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (x : A) (p : parser B C) (CP1 : consuming_parser p) : (parser A C) :=
    fun (stream : stream _) =>
      match p stream with
      | (Ok _, cs', line', col') => (Ok x, cs', line', col')
      | (Err err, cs', line', col') =>
          (Err err, cs', line', col')
      end.

  Lemma consuming_parser_parser_return : forall {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (x : A) (p : parser B C) (CP1 : consuming_parser p),
    consuming_parser (parser_return x p CP1).
  Proof.
    cp_solver.
  Qed.

  (* char: char -> (char, char) parser
    * `char c`
    * Returns a simple parser that expects the next character in the stream to
    * be `c`. Does not consume input upon failure.
    *)
  Definition char (inc : ascii) : (parser ascii ascii) :=
    label ("Expected to see character '" ++ (String inc EmptyString) ++ "'.")
        (satisfy (fun op => (eqb op inc)%char)) (consuming_parser_satisfy (fun op => (eqb op inc)%char)).
  
  (* notChar: char -> (char, char) parser
    * `notChar c`
    * Returns a simple parser that expects the next character in the stream to
    * not be `c`. Does not consume input upon failure.
    *)
  Definition notChar (inc : ascii) : (parser ascii ascii) :=
    label ("Expected not to see character '" ++ (String inc EmptyString) ++ "'.")
        (satisfy (fun op => (negb (eqb op inc)))) (consuming_parser_satisfy (fun op => (negb (eqb op inc)))).

  (* oneOf: char list -> (char, char) parser
    * `oneOf cs`
    * A parser that succeeds exactly when the next character in the stream is
    * one of the characters in the list `cs`. Does not consume input upon
    * failure.
    *)
  Definition oneOf (incs : list ascii) : (parser ascii ascii) :=
      label ("Expected one of the following characters """ ++ (String.string_of_list_ascii incs) ++ """.")
          (satisfy (fun inc => if (List.in_dec (EqClass_impl_DecEq _) (inc) incs) then true else false))
          (consuming_parser_satisfy (fun inc => if (List.in_dec (EqClass_impl_DecEq _) (inc) incs) then true else false)).

  (* noneOf: char list -> (char, char) parser
    * `noneOf cs`
    * A parser that succeeds exactly when the next character in the stream is
    * not one of the characters in the list `cs`. Does not consume input upon
    * failure.
    *)
  Definition noneOf (incs : list ascii) : (parser ascii ascii) :=
      label ("Expected not to see any of the following characters """ ++ (String.string_of_list_ascii incs) ++ """.")
          (satisfy (fun inc => if (List.in_dec (EqClass_impl_DecEq _) inc incs) then false else true))
          (consuming_parser_satisfy (fun inc => if (List.in_dec (EqClass_impl_DecEq _) inc incs) then false else true)).

  (* anyChar: (char, char) parser
    * A simple parser that succeeds so long as there is another character in
    * the stream. Does not consume input upon failure.
    *)
  Definition anyChar : (parser ascii ascii) := 
    label "Expected any character." (satisfy (fun x => true))
      (consuming_parser_satisfy (fun x => true)).

  (* digit: (char, char) Parser
    * A simple parser that succeeds upon seeing a digit, '0'..'9'. Does not
    * consume input upon failure.
    *)
  Definition digit : (parser ascii ascii) := 
    label "Expected a digit." (satisfy CharExtra.isDigit)
      (consuming_parser_satisfy CharExtra.isDigit).


  (* octalDigit: (char, char) Parser
    * A simple parser that succeeds upon seeing an octal numeral, '0'..'7'.
    * Does not consume input upon failure.
    *)
  Definition octalDigit : (parser ascii ascii) := 
      label "Expected an octal digit." (satisfy CharExtra.isOctal)
        (consuming_parser_satisfy CharExtra.isOctal).
  (* hexDigit: (char, char) Parser
    * A simple parser that succeeds upon seeing a hexadecimal numeral,
    * '0'..'9' or 'a'..'f' or 'A'..'F'. Does not consume input upon
    * failure.
    *)
  Definition hexDigit : (parser ascii ascii) := 
      label "Expected a hexidecimal digit." (satisfy CharExtra.isHex)
        (consuming_parser_satisfy CharExtra.isHex).
  (* lower: (char, char) Parser
    * A simple parser that succeeds upon seeing a lowercase ASCII
    * character, 'a'..'z'. Does not consume input upon failure.
    *)
  Definition lower : (parser ascii ascii) := 
      label
          "Expected a lower-case ascii character."
          (satisfy CharExtra.isLower)
        (consuming_parser_satisfy CharExtra.isLower).
  (* upper: (char, char) Parser
    * A simple parser that succeeds upon seeing an uppercase ASCII
    * character, 'A'..'Z'. Does not consume input upon failure.
    *)
  Definition upper : (parser ascii ascii) := 
      label
          "Expected an upper-case ascii character."
          (satisfy CharExtra.isUpper)
        (consuming_parser_satisfy CharExtra.isUpper).

  (* letter: (char, char) Parser
    * A simple parser that succeeds upon seeing an ASCII alphabet
    * character, 'a'..'z' or 'A'..'Z'. Does not consume input upon failure.
    *)
  Definition letter : (parser ascii ascii) := 
      label
          "Expected an ascii alphabet character."
          (satisfy CharExtra.isAlpha)
        (consuming_parser_satisfy CharExtra.isAlpha).
  (* alphaNum: (char, char) Parser
    * A simple parser that succeeds upon seeing an ASCII digit or alphabet
    * character: 'a'..'z', 'A'..'Z', or '0'..'9'. Does not consume input
    * upon failure.
    *)
  Definition alphaNum : (parser ascii ascii) := 
      label
          "Expected an ascii alphanumeric character."
          (satisfy CharExtra.isAlphaNum)
        (consuming_parser_satisfy CharExtra.isAlphaNum).
  (* space: (char, char) Parser
    * A simple parser that succeeds upon seeing any ASCII whitespace
    * characters. Does not consume input upon failure.
    *)
  Definition space : (parser ascii ascii) := 
      label
          "Expected an ascii whitespace character."
          (satisfy CharExtra.isSpace)
        (consuming_parser_satisfy CharExtra.isSpace).

  (*
    Helper for moving the lines and columns while parsing
  *)
  Fixpoint advancePos (cs' : list ascii) (lc : nat * nat) :=
    let (line', col') := lc in
    match cs' with
    | nil => (line', col')
    | c::cs'' => 
        if (eqb c newline)
        then advancePos cs'' (1 + line', 1) 
        else advancePos cs'' (line', 1 + col')
    end.

  (*
    Checks that the "exists l3, l1 ++ l3 = l2" essentially
  *)
  Fixpoint list_prefix {A : Type} `{EqClass A} (l1 l2 : list A) : bool :=
    match l1, l2 with
    | nil, _ => true
    | h1 :: t1, h2 :: t2 => if (eqb h1 h2) then (list_prefix t1 t2) else false
    | _, _ => false
    end.

  (* 
    Drops the first 'n' elements of a list (if it goes off the end it just returns nill)
  *)
  Fixpoint list_drop {A : Type} `{EqClass A} (n : nat) (l : list A) : list A :=
    match n with
    | 0 => l
    | S n' => 
        match l with
        | nil => nil (* TODO: Does this fit spec? *)
        | h :: t => list_drop n' t
        end
    end.

  Lemma list_drop_sn : forall {A : Type} `{EqClass A} ls,
    (forall n, length (list_drop (S n) ls) < length ls) \/ ls = nil.
  Proof.
    induction ls; intros.
    - eauto.
    - destruct IHls.
      * left; intros; destruct n; simpl; try lia.
        destruct ls; try lia.
        pose proof (H0 n). simpl in *. lia.
      * subst. left; simpl. destruct n; eauto.
  Qed.

  (* string: string -> (string, char) parser
  * `string str`
  * A parser that succeeds when the characters of `str` are the characters
  * that appear next in the stream. Does not consume input upon failure.
  *)
  Definition parser_string (str : string) (HS : str <> EmptyString): (parser string ascii) :=
    fun (s : stream _) =>
      match s with
      | (cs, line, col) =>
        let chars := String.list_ascii_of_string str in
            if list_prefix chars cs
            then
                let (line', col') := advancePos chars (line, col)
                in
                    (Ok str, list_drop (String.length str) cs, line', col')
            else (Err ("Expect the literal string """ ++ str ++ """"),
                    cs, line, col)
      end.

  Lemma consuming_parser_parser_string : forall (str : string) (HS : str <> EmptyString),
    consuming_parser (parser_string str HS).
  Proof.
    econstructor; intros.
    inv H.
    destruct str eqn:STR; try congruence;
    destruct (list_drop_sn cs);
    destruct (list_prefix (String.list_ascii_of_string (String a s)) cs) eqn:CS; 
    try (cp_solver; eauto; lia); try congruence.
    destruct (advancePos (String.list_ascii_of_string (String a s)) (line, col)) eqn:AP; inv H1.
    destruct cs; eauto.
  Qed.

  Hint Resolve consuming_parser_parser_string : CP_db.

  Definition carriage_return : ascii := "013".

  (* crlf: (char, char) parser
    * A simple parser that succeeds upon seeing '\r\n' and returns '\n'. Does
    * not consume input upon failure.
    *)
  Example not_empty_1 :
    String carriage_return (String newline EmptyString) <> EmptyString.
  Proof. intros HC; inv HC. Qed.

  Definition crlf :=
      label "Expected a carriage return followed by a line feed."
          (parser_return newline (parser_string (String carriage_return (String newline EmptyString)) not_empty_1) 
          (consuming_parser_parser_string (String carriage_return (String newline EmptyString)) not_empty_1)).

  (* choice: (('a, 'b) parser) list -> ('a, 'b) parser
    * `choice ps`
    * A parser that tries one parser after another until one succeeds or one
    * fails and consumes input. Should the next parser to try fails and
    * consumes input, then this function will do the same.
    *)
  Lemma weaken_CPL : forall {A B : Type} `{EqClass A, EqClass B} 
      (ps : list (parser A B)) p' ps',
    ps = p' :: ps' ->
    (forall p, In p ps -> consuming_parser p) ->
    (forall p, In p ps' -> consuming_parser p).
  Proof.
    intros.
    eapply H2. subst. simpl; eauto.
  Qed.

  Fixpoint choice {A B : Type} `{HA : EqClass A} `{HB : EqClass B} 
      (ps : list (parser A B)) (CPL : forall p, In p ps -> consuming_parser p) (stream : stream B) {struct ps} 
      : (res A string * list B * nat * nat).
  refine (
      (match stream with
      | (cs, line, col) =>
        match ps as l return ps = l -> _  with
        | nil => fun Hyp => (Err "No more parsers to try", cs, line, col)
        | p::ps' =>
          fun Hyp => 
            match p (cs, line, col) with
            | (Ok x, cs', line', col') =>
                (Ok x, cs', line', col')
            | (Err err, cs', line', col') =>
                if (eqb line line') && (eqb col col') && (eqb cs cs')
                then @choice A B HA HB ps' (weaken_CPL ps p ps' Hyp CPL) (cs, line, col)
                else (Err err, cs', line', col')
            end
      end
    end) (eq_refl ps)
  ).
  Defined.

  Lemma consuming_parser_choice : forall {A B : Type} `{HA : EqClass A} `{HB : EqClass B} 
      (ps : list (parser A B)) (CPL : forall p, In p ps -> consuming_parser p) (stream : stream B),
    consuming_parser (fun stream => choice ps CPL stream).
  Proof.
    econstructor. generalize dependent CPL. generalize dependent stream0.
    induction ps as [| a l]; simpl in *; intros.
    - inv H.
    - destruct (a (cs, line, col)) eqn:P1, p, p, r.
      * eapply CPL; inv H; eauto.
      * destruct ((line =? n0)%nat && (col =? n)%nat && general_list_eq_class_eqb cs l0);
        try congruence.
        eapply IHl; eauto.
  Qed.

  Hint Resolve consuming_parser_choice : CP_db.

  (* try: ('a, 'b) parser -> ('a, 'b) parser
    * `try p`
    * Tries parser `p` remembering the state of the stream so that if it fails
    * and consumes input, then `try p` fails but does _not_ consume input.
    *)
  Definition parser_try {A B : Type} `{EqClass A, EqClass B} (p : parser A B) (CP : consuming_parser p) := 
    fun stream =>
      match stream with
      | (cs, line, col) =>
        match p (cs, line, col) with
        | (Err err, _, _, _) => (Err err, cs, line, col)
        | (Ok x, cs', line', col') => (Ok x, cs', line', col')
        end
      end.

  Lemma consuming_parser_parser_try : forall {A B : Type} `{EqClass A, EqClass B} (p : parser A B) 
      (CP : consuming_parser p),
    consuming_parser (parser_try p CP).
  Proof.
    cp_solver.
  Qed.

  (* many: ('a, 'b) parser -> ('a list, 'b) parser
    * `many p`
    * Tries parser `p` zero or more times. As long as `p` succeeds, `many p`
    * will continue to consume input. Once `p` fails whether it has consumed
    * input or not, `many p` succeeds returning the empty list withut consuming
    * input.
    *)
  Require Import Program.
  Program Fixpoint many_sub_parser {A B : Type} `{EqClass A, EqClass B}
      (p : parser A B) (CP : consuming_parser p) (cs : list B) line col {measure (List.length cs)} : ((res (list A) string) * (list B) * nat * nat) :=
      match cs with
      | nil => (* TODO: Is this valid? *)
          (Ok nil, cs, line, col)
      | c :: cs' =>
        match p (cs, line, col) with
        | (Ok x, cs', line', col') => 
            match many_sub_parser p CP cs' line' col' with
            | ((Ok xs), cs'', line'', col'') => (Ok (x::xs), cs'', line'', col'')
            | (Err _, _, _ , _) => (Ok nil, cs, line, col)
            end
        | (Err _, _, _, _) => (Ok nil, cs, line, col)
        end
      end.
  Next Obligation.
    symmetry in Heq_anonymous.
    destruct CP.
    destruct (consuming_always0 _ _ _ _ _ _ _ Heq_anonymous); eauto. 
    inv Heq_anonymous.
    simpl. lia.
  Qed.
(* 
  Lemma consuming_parser_many_sub_parser : forall {A B : Type} `{EqClass A, EqClass B}
      (p : parser A B) (CP : consuming_parser p) (cs : list B) line col,
    consuming_parser (fun _ => many_sub_parser p CP cs line col).
  Proof.
    econstructor. induction cs; intros.
    - cbv in H1. inv H1. eauto.
    - cbv in H1. *)

  Definition many {A B : Type} `{EqClass A, EqClass B} (p : parser A B) (CP : consuming_parser p) : (parser (list A) B) := 
    fun stream => 
      let (csLine, col) := stream in
      let (cs, line) := csLine in
        many_sub_parser p CP cs line col.

  Lemma consuming_parser_many : forall {A B : Type} `{EqClass A, EqClass B} (p : parser A B) 
      (CP : consuming_parser p),
    consuming_parser (many p CP).
  Proof.
    (* econstructor. intros cs.
    generalize dependent p.
    induction cs; intros; simpl in *.
    - cbv in H1. inv H1; eauto.
    - destruct (p ((a :: cs), line, col)) eqn:Ps.
      cbv delta [many_sub_parser] in H1. simpl in H1.
      cbv delta [many_sub_parser_func ] in H1. simpl in H1.
    simpl in H1. *)
  Admitted.

  (* many1: ('a, 'b) parser -> ('a list, 'b) parser
    * `many1 p`
    * Tries parser `p` one or more times. As long as `p` succeeds, `many1 p`
    * will continue to consume input.
    *)
  Definition many1 {A B : Type} `{EqClass A, EqClass B} (p : parser A B) (CP : consuming_parser p) 
      : (parser (list A) B) :=
    fun stream =>
      bind p (fun x => map (fun xs => x::xs) (many p CP) (consuming_parser_many p CP)) CP 
        (fun x => (consuming_parser_map (fun xs => x::xs) (many p CP) (consuming_parser_many p CP))) stream.

  Lemma consuming_parser_many1 : forall {A B : Type} `{EqClass A, EqClass B} (p : parser A B) 
      (CP : consuming_parser p),
    consuming_parser (many1 p CP).
  Proof.
    econstructor; intros.
    unfold many1 in H1. 
    eapply (@consuming_parser_bind A B (list A) _ _ _ p CP _ _).
    eapply H1.
  Qed.

  (* skipMany: ('a, 'b) parser -> (unit, 'b) parser
    * `skipMany p`
    * Tries parser `p` zero or more times, discarding the results. As long as
    * `p` succeeds, `skipMany p` will consume input. Succeeds the first time
    * `p` fails and does not consume input. Should `p` fail and consume input,
    * then so does this function.
    *)
  Program Fixpoint skipMany_rec {A B : Type} `{EqClass A, EqClass B} (p : parser A B) 
      (CP : consuming_parser p) cs line col {measure (length cs)} := 
    match cs with
    | nil => (Err "Ran out of tokens in skipMany_rec", cs, line, col)
    | c :: cs' =>
      match p (cs, line, col) with
      | (Ok _, cs', line', col') => skipMany_rec p CP cs' line' col'
      | (Err err, cs', line', col') =>
          if (eqb line line') && (eqb col col') && (eqb cs cs')
          then (Ok unit_val, cs, line, col)
          else (Err err, cs', line', col')
      end
    end.
  Next Obligation.
    symmetry in Heq_anonymous.
    destruct CP.
    pose proof (consuming_always0 _ _ _ _ _ _ _ Heq_anonymous).
    destruct H1; subst; eauto.
    inv Heq_anonymous. 
    simpl; lia.
  Qed.

  Definition skipMany {A B : Type} `{EqClass A, EqClass B} (p : parser A B) (CP : consuming_parser p) := 
    fun stream =>
      match stream with
      | (cs, line, col) =>
        skipMany_rec p CP cs line col
      end.

  Lemma consuming_parser_skipMany : forall {A B : Type} `{EqClass A, EqClass B, EqClass cml_unit} 
      (p : parser A B) (CP : consuming_parser p),
    consuming_parser (skipMany p CP).
  Proof.
  Admitted.

  (* spaces: (unit, char) parser
    * `spaces = skipMany space`
    * Skips zero or more ASCII whitespace characters. Does not consume input
    * upon failure.
    *)
  Definition spaces `{EqClass cml_unit} : (parser cml_unit ascii) := 
    skipMany space (consuming_parser_label _ _ _).
  (* count: int -> ('a, 'b) parser -> ('a list, 'b) parser
    * `count n p`
    * Applies the parser `p` at most `n` times or until the first time `p`
    * fails. Consumes input whenever `p` does so.
    *)
  Fixpoint count_rec {A B : Type} `{EqClass A, EqClass B} (n : nat)
      (p : parser A B) (CP : consuming_parser p) {struct n} : (parser (list A) B) :=
    fun (stream : stream B) =>
      match stream with
      | (cs, line, col) =>
        match n with
        | 0 => (Err "Never go 0", cs, line, col)
        | S n' =>
          match n' with
          | 0 => 
            match (p (cs, line, col)) with
            | (Ok res, cs', line', col') => (Ok (res :: nil), cs', line', col')
            | (Err err, cs', line', col') => (Err err, cs', line', col')
            end
          | S n0 =>
              match (p (cs, line, col)) with
              | (Ok res, cs', line', col') =>  
                  match ((count_rec n' p CP) (cs', line', col')) with
                  | (Ok res', cs'', line'', col'') => (Ok (res :: res'), cs'', line'', col'')
                  | (Err err, cs'', line'', col'') => (Err err, cs'', line'', col'')
                  end
              | (Err err, cs', line', col') => (Err err, cs', line', col')
              end
          end
        end
      end.

  Lemma consuming_parser_count_rec : forall {A B : Type} `{EqClass A, EqClass B} (n : nat)
      (p : parser A B) (CP : consuming_parser p),
    consuming_parser (count_rec n p CP).
  Proof.
    (* assert (n = 0 \/ n = 1 \/ exists n', n = S (S n')) *)
    econstructor.
    generalize dependent p.
    induction n; intros.
    - inv H1.
    - simpl in H1. 
      destruct n eqn:N.
      * (* n = 0*)
        destruct (p (cs, line, col)) eqn:PS, p0, p0, r; try inv H1.
        eapply CP; eauto.
      * (* n = S n0 *)
        destruct (p (cs, line, col)) eqn:PS, p0, p0, r.
        ** (* success *) 
          destruct (count_rec (S n0) p CP (l, n2, n1)) eqn:PS', p0, p0, r.
          *** (* count_rec success *)
              pose proof (IHn p CP l n2 n1 l0 n4 n3 l1 PS'); inv H1;
              destruct CP;
              pose proof (consuming_always0 _ _ _ _ _ _ _ PS);
              destruct H1, H2; eauto; try lia.
              inv H1. simpl in H2. lia.
          *** (* count_rec err *) inv H1.
        ** (* err *) inv H1.
  Qed.

  Definition count {A B : Type} `{EqClass A, EqClass B} 
      (n : nat) (p : parser A B) (CP : consuming_parser p) : (parser (list A) B) := 
    count_rec n p CP.

  Lemma consuming_parser_count : forall {A B : Type} `{EqClass A, EqClass B} 
      (n : nat) (p : parser A B) (CP : consuming_parser p),
    consuming_parser (count n p CP).
  Proof.
    cbv delta [count]. simpl. intros. eapply consuming_parser_count_rec.
  Qed.
  
  (* between: ('a, 'b) parser -> ('c, 'b) parser -> ('d, 'b) parser -> ('d, 'b) parser
    * `between open close p`
    * Runs parser `open`, then runs `p`, then `close` keeping only the result
    * of `p` upon success.
    *)
  Definition between openp closep p stream := 
      bind openp (fn _ => bind p (fn x => return x closep)) stream
  (* option: 'a -> ('a, 'b) parser -> ('a, 'b) parser
    * `option x p`
    * Runs parser `p` and succeeds returning `x` should `p` fail and not
    * consume input. If `p` succeeds, then this function returns whatever
    * result `p` produces. If `p` fails and consumes input, then this function
    * does the same.
    *)
  Definition option x p (cs, line, col) := 
      case p (cs, line, col) of
        (Ok y, cs', line', col') => (Ok y, cs', line', col')
      | (Err err, cs', line', col') =>
          if line = line' andalso col = col' andalso cs = cs'
          then (Ok x, cs, line, col)
          else (Err err, cs', line', col')
  (* optionOpt: ('a, 'b) parser -> ('a option, 'b) parser
    * Runs parser `p` and succeeds returning `None` should `p` fail and not
    * consume input.
    *)
  (* Definition optionOpt p (cs, line, col) := 
      case p (cs, line, col) of
        (Ok x, cs', line', col') => (Ok (Some x), cs', line', col')
      | (Err err, cs', line', col') =>
          if line = line' andalso col = col' andalso cs = cs'
          then (Ok None, cs, line, col)
          else (Err err, cs', line', col') *)
  (* sepBy: ('a, 'b) parser -> ('c, 'b) parser -> ('a list, 'b) parser
    * `sepBy p sep`
    * Runs zero or more iterations of `p` separated by iterations of `sep` and
    * only the results of `p` are retained. Does not consume input upon
    * failure.
    *)
  Definition sepBy p sepp (cs, line, col) := 
      case p (cs, line, col) of
        (Err _, _, _, _) => (Ok [], cs, line, col)
      | (Ok x, cs', line', col') =>
          case sepp (cs', line', col') of
            (Err _, _, _, _) =>
              (Ok [x], cs', line', col')
          | (Ok _, cs'', line'', col'') =>
              map (fn xs => x::xs) (sepBy p sepp) (cs'', line'', col'')
              (* let
                  val (Ok xs, cs''', line''', col''') := 
                      sepBy p sepp (cs'', line'', col'')
              in
                  (Ok (x::xs), cs''', line''', col''')
              end *)
  (* sepEndBy: ('a, 'b) parser -> ('c, 'b) parser -> ('a list, 'b) parser
    * `sepEndBy p sep`
    * Runs zero or more iterations of `p` interspersed with `sep` and an
    * optional instance of `sep` at the end. Only the results of `p` are
    * retained. Does not consume input upon failure.
    *)
  Definition sepEndBy p sepp (cs, line, col) := 
      case p (cs, line, col) of
        (Err _, _, _, _) => (Ok [], cs, line, col)
      | (Ok x, cs', line', col') =>
          case sepp (cs', line', col') of
            (Err _, _, _, _) =>
              (Ok [x], cs', line', col')
          | (Ok _, cs'', line'', col'') =>
              map (fn xs => x::xs) (sepEndBy p sepp) (cs'', line'', col'')
  (* manyTill: ('a, 'b) parser -> ('c, 'b) parser -> ('a list, 'b) parser
    * `manyTill p endp`
    * Until `endp` succeeds, run parser `p` and only keeps its results. When
    * `endp` fails, whether or not it consumes input, this function backtracks
    * and then applies `p`.
    *)
  Definition manyTill p endp stream := 
      case endp stream of
        (Ok _, cs', line', col') => (Ok [], cs', line', col')
      | (Err _, _, _, _) =>
          case p stream of
            (Err err, cs', line', col') =>
              (Err err, cs', line', col')
          | (Ok x, cs', line', col') =>
              map (fn xs => x::xs) (manyTill p endp) (cs', line', col')
              (* let
                  val (xsr, cs'', line'', col'') := 
                      manyTill p endp (cs', line', col')
              in
                  case xsr of
                    Ok xs => (Ok (x::xs), cs'', line'', col'')
                  | Err err => (Err err, cs'', line'', col'')
              end *)

  (* ('a, 'c) parser -> ('b, 'c) parser -> ('a, 'c) parser *)
  Definition followedBy p q = bind p (fn a => return a q)

  (* ('a, char) parser -> ('a, char) parser *)
  (* Token-based parsing consumes all whitespace after parsing *)
  Definition token p = followedBy p spaces

  (* (string, char) parser *)
  Definition symbol s = token (string s)