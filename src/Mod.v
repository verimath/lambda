(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Modules *)

Set Implicit Arguments.

Require Export Monad.
Require Import Extensionality.

(** ** Notations *)

Reserved Notation "x >>>= f" (at level 42, left associativity).
Reserved Notation "x >>>- f" (at level 42, left associativity).

(** ** Definition of module of a monad. *)

Implicit Type X Y Z : Set.

Record Mod (P : Monad) : Type := {
  mod_carrier :> Set -> Set;
  mbind : forall X Y (f : X -> P Y) (x : mod_carrier X),
    mod_carrier Y;
  mbind_mbind : forall X Y Z
    (f : X -> P Y) (g : Y -> P Z) (x : mod_carrier X),
    mbind Z g (mbind Y f x) = mbind Z (fun u => f u >>= g) x;
  unit_mbind : forall X (x : mod_carrier X),
    mbind X (@unit P X) x = x
}.

Notation "x >>>= f" := (@mbind _ _ _ _ f x).

Hint Rewrite mbind_mbind unit_mbind : mod.

Hint Extern 1 (_ = _ :> @mod_carrier _ _ _) => autorewrite with mod : mod.

Ltac mod := intros; autorewrite with monad mod; auto with mod monad.

Definition mmap (P : Monad) (T : Mod P)
  X Y (f : X -> Y) (x : T X) : T Y :=
  x >>>= fun x => unit P (f x).

Notation "x >>>- f" := (@mmap _ _ _ _ f x).

Definition mlift (P : Monad) (T : Mod P) X Y (f : X -> Y) : T X -> T Y :=
  @mbind P T _ _ (fun x => unit P (f x)).

Definition mlift2 (P : Monad) (T : Mod P) X Y Z
  (f : X -> Y -> Z) (a : P X) (b : T Y) : T Z :=
  b >>>= (fun y => a >>= fun x => unit P (f x y)).

Section Mod_Facts.

Variable P : Monad.
Variable M : Mod P.

Lemma mbind_congr : forall X Y (f g : X -> P Y) (x y : M X),
  x = y -> (forall a, f a = g a) -> x >>>= f = y >>>= g.
Proof.
intros. subst y. replace g with f. reflexivity.
apply extensionality. trivial.
Qed.

Hint Resolve mbind_congr : mod.

Lemma unit_mbind_match : forall X (f : X -> P X) (x : M X),
  (forall a, f a = unit P a) -> x >>>= f = x.
Proof.
intros.
transitivity (x >>>= @unit P X).
apply mbind_congr; trivial.
auto with mod.
Qed.

Lemma mmap_mbind : forall X Y Z (f : X -> P Y) (g : Y -> Z) (x : M X),
  x >>>= f >>>- g = x >>>= (fun u => f u >>- g).
Proof.
unfold mmap; mod.
Qed.

Lemma mbind_mmap : forall X Y Z (f : X -> Y) (g : Y -> P Z) (x : M X),
  x >>>- f >>>= g = x >>>= fun u : X => g (f u).
Proof.
unfold mmap. mod.
Qed.

Lemma mmap_mmap : forall X Y Z (f : X -> Y) (g : Y -> Z) (x : M X),
  x >>>- f >>>- g = x >>>- fun u : X => g (f u).
Proof.
unfold mmap. mod.
Qed.

End Mod_Facts.

Hint Resolve unit_mbind_match mbind_congr : mod.
Hint Rewrite mmap_mbind mbind_mmap mmap_mmap : mod.

Record Mod_Hom (P : Monad) (S T : Mod P) : Type := {
  mod_hom_carrier :> forall X, S X -> T X;
  mod_hom_mbind : forall X Y (f : X -> P Y) (x : S X),
    mod_hom_carrier Y (x >>>= f) = mod_hom_carrier X x >>>= f
}.

Hint Rewrite mod_hom_mbind : mod.

(** ** Tautological module *)

Definition Taut_Mod (P : Monad) : Mod P :=
  Build_Mod P P (@bind P) (@bind_bind P) (@unit_bind P).

Coercion Taut_Mod : Monad >-> Mod.

(** ** Pull-back module *)

Section Pull_back.

Variable (P Q: Monad) (h : Monad_Hom P Q) (M : Mod Q).

Let bb X Y (f : X -> P Y) (x : M X) : M Y :=
  x >>>= fun u => h Y (f u).

Remark bb_bb : forall X Y Z (f : X -> P Y) (g : Y -> P Z) (x : M X),
  bb Z g (bb Y f x) = bb Z (fun u : X => f u >>= g) x.
Proof.
unfold bb; mod.
Qed.

Remark unit_bb : forall X (x : M X),
  bb X (unit P (X:=X)) x = x.
Proof.
unfold bb; mod.
Qed.

Definition PB : Mod P := Build_Mod P M bb bb_bb unit_bb.

End Pull_back.
