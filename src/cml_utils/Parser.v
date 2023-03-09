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
  Definition eof {A : Type} :=
    fun (stream : stream string) =>
      match stream with
      | (cs, line, col) =>
        match cs with
        | nil => (Ok unit_val, cs, line, col)
        | c::cs' => (Err "End of stream expected.", c::cs', line, col)
        end
      end.

  (* TODO: THIS DOESNT WORK *) 
  (* Lemma consuming_parser_eof : forall {A : Type},
    consuming_parser eof. *)
  
  (* seq: parser A B -> parser C B -> parser C B
    * `seq p1 p2`
    * Runs parser `p1` and then, upon success, runs parser `p2`, discarding the
    * previous results.
    *)
  Definition seq {A B C: Type} `{EqClass A, EqClass B, EqClass C}
      (p1 : parser A B) (p2 : parser C B) (CP1 : consuming_parser p1) (CP2 : consuming_parser p2) : (parser C B) :=
    fun (s : stream B) => 
      bind p1 (fun _ => p2) s.

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

    (* label: string -> ('a, 'b) parser -> ('a, 'b) parser
    * `label errMsg p`
    * Runs parser `p` and if it fails without consuming input, then the error
    * message is replaced by `errMsg`.
    *)
  Definition label {A B : Type} `{EqClass A, EqClass B}
      (errMsg : string) (p : parser A B) : (parser A B) :=
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

  (* parser_return: 'a -> ('b, 'c) parser -> ('a, 'c) parser
    * `parser_return x p`
    * Runs parser `p` and if it succeeds replace the result with `x`.
    *)
  Definition parser_return {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (x : A) (p : parser B C) : (parser A C) :=
    fun (stream : stream _) =>
      match p stream with
      | (Ok _, cs', line', col') => (Ok x, cs', line', col')
      | (Err err, cs', line', col') =>
          (Err err, cs', line', col')
      end.

  (* char: char -> (char, char) parser
    * `char c`
    * Returns a simple parser that expects the next character in the stream to
    * be `c`. Does not consume input upon failure.
    *)
  Definition char (inc : ascii) : (parser ascii ascii) :=
    label ("Expected to see character '" ++ (String inc EmptyString) ++ "'.")
        (satisfy (fun op => (eqb op inc)%char)).
  
  (* notChar: char -> (char, char) parser
    * `notChar c`
    * Returns a simple parser that expects the next character in the stream to
    * not be `c`. Does not consume input upon failure.
    *)
  Definition notChar (inc : ascii) : (parser ascii ascii) :=
    label ("Expected not to see character '" ++ (String inc EmptyString) ++ "'.")
        (satisfy (fun op => (negb (eqb op inc)))).

  (* oneOf: char list -> (char, char) parser
    * `oneOf cs`
    * A parser that succeeds exactly when the next character in the stream is
    * one of the characters in the list `cs`. Does not consume input upon
    * failure.
    *)
  Definition oneOf (incs : list ascii) : (parser ascii ascii) :=
      label ("Expected one of the following characters """ ++ (String.string_of_list_ascii incs) ++ """.")
          (satisfy (fun inc => if (List.in_dec (EqClass_impl_DecEq _) (inc) incs) then true else false)).

  (* noneOf: char list -> (char, char) parser
    * `noneOf cs`
    * A parser that succeeds exactly when the next character in the stream is
    * not one of the characters in the list `cs`. Does not consume input upon
    * failure.
    *)
  Definition noneOf (incs : list ascii) : (parser ascii ascii) :=
      label ("Expected not to see any of the following characters """ ++ (String.string_of_list_ascii incs) ++ """.")
          (satisfy (fun inc => if (List.in_dec (EqClass_impl_DecEq _) inc incs) then false else true)).

  (* anyChar: (char, char) parser
    * A simple parser that succeeds so long as there is another character in
    * the stream. Does not consume input upon failure.
    *)
  Definition anyChar := label "Expected any character." (satisfy (fun x => true)).

  (* digit: (char, char) Parser
    * A simple parser that succeeds upon seeing a digit, '0'..'9'. Does not
    * consume input upon failure.
    *)
  Definition digit := label "Expected a digit." (satisfy CharExtra.isDigit).


  (* octalDigit: (char, char) Parser
    * A simple parser that succeeds upon seeing an octal numeral, '0'..'7'.
    * Does not consume input upon failure.
    *)
  Definition octalDigit := 
      label "Expected an octal digit." (satisfy CharExtra.isOctal).
  (* hexDigit: (char, char) Parser
    * A simple parser that succeeds upon seeing a hexadecimal numeral,
    * '0'..'9' or 'a'..'f' or 'A'..'F'. Does not consume input upon
    * failure.
    *)
  Definition hexDigit := 
      label "Expected a hexidecimal digit." (satisfy CharExtra.isHex).
  (* lower: (char, char) Parser
    * A simple parser that succeeds upon seeing a lowercase ASCII
    * character, 'a'..'z'. Does not consume input upon failure.
    *)
  Definition lower := 
      label
          "Expected a lower-case ascii character."
          (satisfy CharExtra.isLower).
  (* upper: (char, char) Parser
    * A simple parser that succeeds upon seeing an uppercase ASCII
    * character, 'A'..'Z'. Does not consume input upon failure.
    *)
  Definition upper := 
      label
          "Expected an upper-case ascii character."
          (satisfy CharExtra.isUpper).
  (* letter: (char, char) Parser
    * A simple parser that succeeds upon seeing an ASCII alphabet
    * character, 'a'..'z' or 'A'..'Z'. Does not consume input upon failure.
    *)
  Definition letter := 
      label
          "Expected an ascii alphabet character."
          (satisfy CharExtra.isAlpha).
  (* alphaNum: (char, char) Parser
    * A simple parser that succeeds upon seeing an ASCII digit or alphabet
    * character: 'a'..'z', 'A'..'Z', or '0'..'9'. Does not consume input
    * upon failure.
    *)
  Definition alphaNum := 
      label
          "Expected an ascii alphanumeric character."
          (satisfy CharExtra.isAlphaNum).
  (* space: (char, char) Parser
    * A simple parser that succeeds upon seeing any ASCII whitespace
    * characters. Does not consume input upon failure.
    *)
  Definition space := 
      label
          "Expected an ascii whitespace character."
          (satisfy CharExtra.isSpace).

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
  Fixpoint list_drop {A : Type} `{EqClass A} (l : list A) (n : nat) : list A :=
    match n with
    | 0 => l
    | S n' => 
        match l with
        | nil => nil (* TODO: Does this fit spec? *)
        | h :: t => list_drop t n'
        end
    end.

  (* string: string -> (string, char) parser
  * `string str`
  * A parser that succeeds when the characters of `str` are the characters
  * that appear next in the stream. Does not consume input upon failure.
  *)
  Definition parser_string (str : string) : (parser string ascii) :=
    fun (s : stream _) =>
      match s with
      | (cs, line, col) =>
        let chars := String.list_ascii_of_string str in
            if list_prefix chars cs
            then
                let (line', col') := advancePos chars (line, col)
                in
                    (Ok str, list_drop cs (String.length str), line', col')
            else (Err ("Expect the literal string """ ++ str ++ """"),
                    cs, line, col)
      end.

  Definition carriage_return : ascii := "013".

  (* crlf: (char, char) parser
    * A simple parser that succeeds upon seeing '\r\n' and returns '\n'. Does
    * not consume input upon failure.
    *)
  Definition crlf :=
      label "Expected a carriage return followed by a line feed."
          (parser_return newline (parser_string (String carriage_return (String newline EmptyString)))).

  (* choice: (('a, 'b) parser) list -> ('a, 'b) parser
    * `choice ps`
    * A parser that tries one parser after another until one succeeds or one
    * fails and consumes input. Should the next parser to try fails and
    * consumes input, then this function will do the same.
    *)
  Fixpoint choice {A B : Type} `{EqClass A, EqClass B} 
      (ps : list (parser A B)) :=
    fun stream =>
      match stream with
      | (cs, line, col) =>
        match ps with
        | nil => (Err "No more parsers to try", cs, line, col)
        | p::ps' =>
          match p (cs, line, col) with
          | (Ok x, cs', line', col') =>
              (Ok x, cs', line', col')
          | (Err err, cs', line', col') =>
              if (eqb line line') && (eqb col col') && (eqb cs cs')
              then choice ps' (cs, line, col)
              else (Err err, cs', line', col')
          end
      end
    end.

  (* try: ('a, 'b) parser -> ('a, 'b) parser
    * `try p`
    * Tries parser `p` remembering the state of the stream so that if it fails
    * and consumes input, then `try p` fails but does _not_ consume input.
    *)
  Definition try {A B : Type} `{EqClass A, EqClass B} (p : parser A B) := 
    fun stream =>
      match stream with
      | (cs, line, col) =>
        match p (cs, line, col) with
        | (Err err, _, _, _) => (Err err, cs, line, col)
        | (Ok x, cs', line', col') => (Ok x, cs', line', col')
        end
      end.
  (* many: ('a, 'b) parser -> ('a list, 'b) parser
    * `many p`
    * Tries parser `p` zero or more times. As long as `p` succeeds, `many p`
    * will continue to consume input. Once `p` fails whether it has consumed
    * input or not, `many p` succeeds returning the empty list withut consuming
    * input.
    *)
  Require Import Program.
  Program Fixpoint many_sub_parser {A B : Type} `{EqClass A, EqClass B}
      (p : parser A B) (cs : list B) line col {measure (List.length cs)} : ((res (list A) string) * (list B) * nat * nat) :=
      match p (cs, line, col) with
      | (Ok x, cs', line', col') => 
          match many_sub_parser p cs' line' col' with
          | ((Ok xs), cs'', line'', col'') => (Ok (x::xs), cs'', line'', col'')
          | (Err _, _, _ , _) => (Ok nil, cs, line, col)
          end
      | (Err _, _, _, _) => (Ok nil, cs, line, col)
      end.
  (* TODO: This is a big admit, this is certainly NOT TRUE, but we need it for now *)
  Admit Obligations.

  Definition many {A B : Type} `{EqClass A, EqClass B} (p : parser A B) : (parser (list A) B) := 
    fun stream => 
      let (csLine, col) := stream in
      let (cs, line) := csLine in
        many_sub_parser p cs line col.
      
  (* many1: ('a, 'b) parser -> ('a list, 'b) parser
    * `many1 p`
    * Tries parser `p` one or more times. As long as `p` succeeds, `many1 p`
    * will continue to consume input.
    *)
  Definition many1 p stream := bind p (fun x => map (fun xs => x::xs) (many p)) stream.
  (* skipMany: ('a, 'b) parser -> (unit, 'b) parser
    * `skipMany p`
    * Tries parser `p` zero or more times, discarding the results. As long as
    * `p` succeeds, `skipMany p` will consume input. Succeeds the first time
    * `p` fails and does not consume input. Should `p` fail and consume input,
    * then so does this function.
    *)
  Fixpoint skipMany p (cs, line, col) := 
      match p (cs, line, col) with
      | (Ok _, cs', line', col') => skipMany p (cs', line', col')
      | (Err err, cs', line', col') =>
          if line = line' andalso col = col' andalso cs = cs'
          then (Ok (), cs, line, col)
          else (Err err, cs', line', col')
      end.
  (* spaces: (unit, char) parser
    * `spaces = skipMany space`
    * Skips zero or more ASCII whitespace characters. Does not consume input
    * upon failure.
    *)
  val spaces = skipMany space
  (* count: int -> ('a, 'b) parser -> ('a list, 'b) parser
    * `count n p`
    * Applies the parser `p` at most `n` times or until the first time `p`
    * fails. Consumes input whenever `p` does so.
    *)
  Definition count n p (cs, line, col) := 
      if n <= 0
      then (Ok [], cs, line, col)
      else
          bind p
              (fn x => map (fn xs => x::xs) (count (n - 1) p))
              (cs, line, col)
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