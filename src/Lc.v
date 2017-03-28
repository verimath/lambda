(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Simple (untyped) Lambda Calculus *)

Set Implicit Arguments.

Require Import Quot.
Require Export Slc.
Opaque app1.

Section Lc.

Implicit Type X Y Z : Set.

Let r X : Eqv (term X) :=
  Build_Eqv (@lcr X) (@lcr_rfl X) (@lcr_sym X) (@lcr_trs X).
Implicit Arguments r [X].

Definition lc : Set -> Set := fun X => term X // r.

Definition lc_class X : term X -> lc X := class r.
Notation "/ x" := (lc_class x).

Lemma lc_class_eq : forall X (x y : term X),
  x == y -> /x = /y.
Proof.
unfold lc_class. intros.
apply class_eq with (r := @r X). assumption.
Qed.
Hint Resolve lc_class_eq.

Lemma lc_class_rel : forall X (x y : term X),
  /x = /y -> x == y.
Proof.
unfold lc_class; simpl. intros.
apply class_rel with (r := @r X). assumption.
Qed.
Hint Resolve lc_class_rel.

Lemma lc_class_surj : forall X (u : lc X),
  exists a, /a = u.
Proof.
unfold r; simpl. intro X.
apply (class_ind (fun u => exists a : term X, / a = u)).
intros. split with x. reflexivity.
Qed.
Hint Resolve lc_class_surj.

Definition lc_factor X Y (f : term X -> Y)
  (Hf : forall x y, x == y -> f x = f y) : lc X -> Y :=
  factor r f Hf.

Lemma lc_factorize : forall X Y (f : term X -> Y)
  (H : forall x y, x == y -> f x = f y),
    forall x,  lc_factor f H (/x) = f x.
Proof.
unfold lc_factor, lc_class; simpl; intros. apply factorize.
Qed.
Hint Resolve lc_factorize.

Lemma lc_factor_cong : forall X Y (f g : term X -> Y) (x : lc X)
  (Hf : forall x y, x == y -> f x = f y)
  (Hg : forall x y, x == y -> g x = g y)
  (H : forall x, f x = g x),
  lc_factor f Hf x = lc_factor g Hg x.
Proof.
intros. unfold lc_factor.
apply factor_extens. assumption.
Qed.

Definition lc_factor1 X Y (f : term X -> term Y)
  (Hf : forall x y, x == y -> f x == f y) : lc X -> lc Y :=
  factor1 r r f Hf.

Lemma lc_factorize1 : forall X Y (f : term X -> term Y)
  (H : forall x y, x == y -> f x == f y),
    forall x,  lc_factor1 f H (/x) = /f x.
Proof.
unfold lc, lc_factor1, lc_class; simpl; intros. apply factorize1.
Qed.
Hint Resolve lc_factorize1.

Definition lc_factor2 X Y Z (f : term X -> term Y -> term Z)
  (Hf : forall x y z w, x == y -> z == w -> f x z == f y w) :
    lc X -> lc Y -> lc Z :=
  factor2 r r r f Hf.

Lemma lc_factorize2 : forall X Y Z (f : term X -> term Y -> term Z)
  (H : forall x y z w, x == y -> z == w -> f x z == f y w),
    forall x y,  lc_factor2 f H (/x) (/y) = /f x y.
Proof.
unfold lc, lc_factor2, lc_class; simpl; intros. apply factorize2.
Qed.
Hint Resolve lc_factorize2.

Lemma lc_fun_lift : forall X Y (f : X -> lc Y),
  exists g : X -> term Y, f = fun x => /g x.
Proof.
intros. lift_fun f f'. exists f'. reflexivity.
Qed.

Opaque lc lc_class lc_factor lc_factor1 lc_factor2.

Definition lc_abs X : lc (option X) -> lc X :=
  lc_factor1 (@abs X) (@lcr_abs X).

Lemma lc_abs_factorize : forall X (x : term (option X)),
  lc_abs (/x) = / abs x.
Proof.
unfold lc_abs. intros. apply lc_factorize1.
Qed.

Opaque lc_abs.

Definition lc_app1 X : lc X -> lc (option X) :=
  lc_factor1 (@app1 X) (@lcr_app1 X).

Lemma lc_app1_factorize : forall X (x : term X),
  lc_app1 (/x) = / app1 x.
Proof.
unfold lc_app1. intros. apply lc_factorize1.
Qed.

Opaque lc_app1.

Definition lc_app X : lc X -> lc X -> lc X :=
  lc_factor2 (@app X) (@lcr_app X).

Lemma lc_app_factorize : forall X (x y : term X),
  lc_app (/x) (/y) = / app x y.
Proof.
unfold lc_app. intros. apply lc_factorize2.
Qed.

Opaque lc_app.

Definition lc_var X (x : X) : lc X := / var x.


Definition lc_fct X Y (f : X -> Y) : lc X -> lc Y :=
  lc_factor1 (fct f) (lcr_fct f).

Lemma lc_fct_factorize : forall X Y (f : X -> Y) (x : term X),
  lc_fct f (/x) = /fct f x.
Proof.
unfold lc_fct; intros. apply lc_factorize1.
Qed.

Opaque lc_fct.

Definition lc_comm X Y (f : X -> lc Y) (x : option X) : lc (option Y) :=
  match x with
  | Some a => lc_fct (@Some Y) (f a)
  | None => lc_var None
  end.

Fixpoint lc_bind_fix X Y (f : X -> lc Y) (x : term X) { struct x } : lc Y :=
  match x with
  | var x => f x
  | app x y => lc_app (lc_bind_fix f x) (lc_bind_fix f y)
  | abs x => lc_abs (lc_bind_fix (lc_comm f) x)
  end.

Lemma lc_bind_fix_fun_cong : forall X (x : term X) Y (f g : X -> lc Y),
  (forall u, f u = g u) -> lc_bind_fix f x = lc_bind_fix g x.
Proof.
induction x; simpl; intros; auto.
f_equal. apply IHx.
destruct u; simpl; auto.
Qed.

Remark lc_bind_fix_factorize : forall X Y (f : X -> term Y) (x : term X),
  lc_bind_fix (fun a => /f a) x = /(x //= f).
Proof.
intros.
generalize Y f; clear Y f.
induction x; simpl; intros.
reflexivity.
rewrite IHx1.
rewrite IHx2.
apply lc_app_factorize.
rewrite <- lc_abs_factorize. f_equal.
rewrite <- IHx.
apply lc_bind_fix_fun_cong.
destruct u; simpl.
rewrite lc_fct_factorize. reflexivity.
reflexivity.
Qed.

Remark lc_bind_fix_wd : forall X Y (f : X -> lc Y) (x y : term X),
  x == y -> lc_bind_fix f x = lc_bind_fix f y.
Proof.
intros. destruct (lc_fun_lift f) as (f', Hf). subst f.
do 2 rewrite lc_bind_fix_factorize. apply lc_class_eq.
apply lcr_bind. intros. apply lcr_rfl. assumption.
Qed.

Definition lc_bind X Y (f : X -> lc Y) : lc X -> lc Y :=
  lc_factor (lc_bind_fix f) (lc_bind_fix_wd f).

Lemma lc_bind_factorize : forall X Y (f : X -> term Y) (x : term X),
  lc_bind (fun a => /f a) (/x) = /(x //= f).
Proof.
unfold lc_bind. intros.
rewrite lc_factorize. apply lc_bind_fix_factorize.
Qed.

Lemma lc_bind_fun_cong : forall X Y (f g : X -> lc Y) (x : lc X),
  (forall u, f u = g u) -> lc_bind f x = lc_bind g x.
Proof.
intros.
unfold lc_bind.
apply lc_factor_cong.
intros.
apply lc_bind_fix_fun_cong.
assumption.
Qed.

Opaque lc_bind.

Lemma lc_fct_as_bind : forall X Y (f : X -> Y) (x : lc X),
  lc_fct f x = lc_bind (fun a => lc_var (f a)) x.
Proof.
unfold lc_var. intros.
destruct (lc_class_surj x) as [y Hy]. subst x.
rewrite lc_fct_factorize. rewrite slc_fct_as_bind.
rewrite <- lc_bind_factorize. reflexivity.
Qed.

Lemma lc_bind_assoc :
  forall X Y Z (f : X -> lc Y) (g : Y -> lc Z) (x : lc X),
  lc_bind g (lc_bind f x) = lc_bind (fun a => lc_bind g (f a)) x.
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_bind_factorize.
destruct (lc_fun_lift g) as (g', Hg). subst g.
rewrite lc_bind_factorize.
rewrite slc_bind_bind.
rewrite <- lc_bind_factorize.
apply lc_bind_fun_cong. intros.
rewrite lc_bind_factorize. reflexivity.
Qed.

Lemma lc_bind_var : forall X Y (f : X -> lc Y) (x : X),
  lc_bind f (lc_var x) = f x.
Proof.
unfold lc_var. intros.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_bind_factorize. rewrite slc_bind_var. reflexivity.
Qed.

Lemma lc_var_bind : forall X (x : lc X),
  lc_bind (@lc_var X) x = x.
Proof.
unfold lc_var. intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_bind_factorize.
rewrite slc_var_bind. reflexivity.
Qed.

Lemma lc_bind_abs : forall X Y (f : X -> lc Y) (x : lc (option X)),
  lc_bind f (lc_abs x) = lc_abs (lc_bind (lc_comm f) x).
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_abs_factorize.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_bind_factorize. simpl.
rewrite <- lc_abs_factorize. f_equal.
rewrite <- lc_bind_factorize.
apply lc_bind_fun_cong. intro.
destruct u; simpl. 2:reflexivity.
rewrite lc_fct_factorize. reflexivity.
Qed.

Lemma lc_bind_app1 : forall X Y (f : X -> lc Y) (x : lc X),
  lc_bind (lc_comm f) (lc_app1 x) = lc_app1 (lc_bind f x).
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
destruct (lc_fun_lift f) as (f', Hf). subst f.
rewrite lc_app1_factorize.
rewrite lc_bind_factorize.
rewrite lc_app1_factorize.
transitivity (lc_bind (fun a => /comm f' a) (/ app1 y)).
apply lc_bind_fun_cong.
destruct u; simpl. 2:reflexivity.
rewrite lc_fct_factorize. reflexivity.
rewrite lc_bind_factorize.
rewrite slc_bind_app1. rewrite app1_app.
unfold shift. rewrite slc_fct_bind. reflexivity.
Qed.

Lemma lc_eta : forall X (x : lc X),
  lc_abs (lc_app1 x) = x.
Proof.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_app1_factorize. rewrite lc_abs_factorize.
apply lc_class_eq. apply lcr_eta.
Qed.

Lemma lc_beta : forall X (x : lc (option X)),
  lc_app1 (lc_abs x) = x.
intros.
destruct (lc_class_surj x) as (y, Hy). subst x.
rewrite lc_abs_factorize. rewrite lc_app1_factorize.
apply lc_class_eq. apply lcr_beta. 
rewrite app1_app. unfold shift. simpl.
apply beta_intro_alt. rewrite slc_bind_fct.
apply slc_var_bind_match.
destruct u; reflexivity.
Qed.

End Lc.
