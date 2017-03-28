(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Derived Module *)

Set Implicit Arguments.

Require Export Misc.
Require Export Mod.

Section Derived_Mod.

Implicit Type X Y Z : Set.

Variable (P : Monad) (M : Mod P).

Section Def.

Let T : Set -> Set := fun X => M (option X).

Let bT X Y (f : X -> P Y) (x : T X) : T Y :=
  x >>>= (default (fun u => (f u) >>- @Some Y) (unit P None)).

Remark bT_bT : forall X Y Z (f : X -> P Y) (g : Y -> P Z) (x : T X),
  bT Z g (bT Y f x) = bT Z (fun u : X => f u >>= g) x.
Proof.
unfold T, bT; intros; autorewrite with mod.
apply mbind_congr. reflexivity.
intros. destruct a; simpl; monad.
Qed.

Remark unit_bT : forall X (x : T X),
  bT X (unit P (X:=X)) x = x.
Proof.
unfold T, bT; intros; autorewrite with mod.
apply unit_mbind_match.
destruct a; simpl; mod.
Qed.

Definition Derived_Mod : Mod P := Build_Mod P T bT bT_bT unit_bT.

End Def.

Section Inc.

Let i X (x : M X) : Derived_Mod X := x >>>- @Some X.

Remark i_hom : forall X Y (f : X -> P Y) (x : M X),
  i Y (x >>>= f) = mbind Derived_Mod _ f (i X x).
Proof.
unfold i; simpl; mod.
Qed.

Definition derived_inc : Mod_Hom M Derived_Mod :=
  Build_Mod_Hom _ _ i i_hom.

End Inc.

End Derived_Mod.


(** * Exponetial Monads *)

Record ExpMonad : Type := {
  exp_monad :> Monad;
  exp_abs : Mod_Hom (Derived_Mod exp_monad) exp_monad;
  exp_app : Mod_Hom exp_monad (Derived_Mod exp_monad);
  exp_eta : forall X (x : exp_monad X),
    exp_abs _ (exp_app _ x) = x;
  exp_beta : forall X (x : Derived_Mod exp_monad X),
    exp_app _ (exp_abs _ x) = x
}.

Record ExpMonad_Hom (M N : ExpMonad) : Type := {
  expmonad_hom :> Monad_Hom M N;
  expmonad_hom_app : forall X (x : M X),
    expmonad_hom _ (exp_app M _ x) = exp_app N _ (expmonad_hom _ x);
  expmonad_hom_abs : forall X (x : Derived_Mod M X),
    expmonad_hom _ (exp_abs M _ x) = exp_abs N _ (expmonad_hom _ x)
}.
