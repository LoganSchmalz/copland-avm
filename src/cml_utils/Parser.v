Require Import String Ascii List Nat Bool.
Require Import EqClass.

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

  (* parse: parser A ascii -> string -> res A string
     * `parse p str`
     * Runs the parser `p` over the string `str`.
     *)
  Definition parse {A : Type} `{HA : EqClass A} (p : (parser A ascii)) (str : string) : (res A string) :=
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
  Definition bind {A B C : Type} `{EqClass A, EqClass B, EqClass C} 
      (p : parser A B) (funcp : (A -> (parser C B))) : (parser C B) :=
    fun (stream : stream B) =>
      match (p stream) with
      | (Ok x, cs', line', col') => funcp x (cs', line', col')
      | (Err msg, cs', line', col') => ((Err msg), cs', line', col')
      end.

  (* bindResult: (A -> res B string) -> (parser A C) -> (parser B C)
    * `bindResult func p`
    * Runs the parser `p` and upon success, applies `func` to the result.
    *)
  Definition bindResult {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (func : A -> res B string) (p : parser A C) : (parser B C) :=
    fun (stream : (stream C)) =>
      match p stream with
      | (Ok x, cs', line', col') => (func x, cs', line', col')
      | (Err err, cs', line', col') => (Err err, cs', line', col')
      end.

  (* map: (A -> B) -> parser A C -> parser B C
    * `map func p`
    * returns parser `p` and upon success, applies `func` to the result.
    *)
  Definition map {A B C : Type} `{EqClass A, EqClass B, EqClass C}
      (func : A -> B) (p : parser A C) : (parser B C) :=
    fun (stream : stream C) =>
      match p stream with
      | (Ok x, cs', line', col') =>
          (Ok (func x), cs', line', col')
      | (Err err, cs', line', col') =>
          (Err err, cs', line', col')
      end.

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
  
  (* seq: parser A B -> parser C B -> parser C B
    * `seq p1 p2`
    * Runs parser `p1` and then, upon success, runs parser `p2`, discarding the
    * previous results.
    *)
  Definition seq {A B C: Type} `{EqClass A, EqClass B, EqClass C}
      (p1 : parser A B) (p2 : parser C B) : (parser C B) :=
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