(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Axiom of extensionality *)

Axiom extensionality : forall (X Y : Type) (f g : X -> Y),
  (forall x, f x = g x) -> f = g.

