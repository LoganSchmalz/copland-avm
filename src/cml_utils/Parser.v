Require Import String Ascii.

Inductive res (A B : Type) :=
| Ok : A -> res A B
| Err : B -> res A B.

Definition nat_to_string : nat -> string. Admitted.

Module Type Parser.
  Definition stream (A : Type) : Type := (list A * nat * nat).
  Definition parser (A B : Type) : Type := (stream B) -> ((res A string) * list B * nat * nat).

  Definition parse {A : Type} (p : (parser A ascii)) (str : string) : (res A string) :=
    match (p (String.list_ascii_of_string str , 1, 1)) with
    | (Ok x, _, _ , _) => Ok x
    | (Err msg, _, line, col) => 
        Err ("Error on line " ++ nat_to_string line ++ ", column " ++ nat_to_string col ++ ": " ++ msg)
    end.