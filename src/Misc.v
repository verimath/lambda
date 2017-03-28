(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Miscellanea *)

Set Implicit Arguments.

(** ** Handy terms for [option] *)

Definition optmap (X Y : Set) (f : X -> Y) (x : option X) : option Y := 
  match x with Some a => Some (f a) | new => None end.

Definition default (X Y : Set) (f : X -> Y) (def : Y) (x : option X) : Y :=
  match x with Some a => f a | new => def end.

(** ** An useful hint. *)

Hint Extern 1 (?x = ?y) => f_equal.