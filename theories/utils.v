From Coq Require Import String.

(** Similar to List.skipn. Useful in name transformers. *)
Fixpoint string_drop (n : nat) (s : string) : string :=
  match n with
  | 0 => s
  | S n => match s with
           | EmptyString => ""
           | String _ s => string_drop n s
           end
  end.
