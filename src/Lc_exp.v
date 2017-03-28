(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** * Main theorem of the present contribution *)

(** Proof of the following theorem [iota_unique] :
    "Simple Lambda Calculus is initial in the category of
     exponential monads". *)

Set Implicit Arguments.

Require Export Lc.
Require Export Derived_Mod.

Section Lc_exp.

Implicit Type X Y Z : Set.

Opaque app1.
Opaque lc lc_class lc_factor lc_factor1 lc_factor2.
Opaque lc_abs lc_app1 lc_abs lc_fct lc_bind.

Notation "/ x" := (lc_class x).

Definition SLC : Monad :=
  Build_Monad term slc_bind var slc_bind_bind slc_bind_var slc_var_bind.

Definition LC : Monad := 
  Build_Monad lc lc_bind lc_var lc_bind_assoc lc_bind_var lc_var_bind.

Lemma slc_bind_var : forall X Y (f : X -> SLC Y) (u : X),
  var u >>= f = f u.
Proof.
reflexivity.
Qed.

Lemma slc_bind_app : forall X Y (f : X -> SLC Y) (x y : SLC X),
  app x y >>= f = app (x >>= f)  (y >>= f).
Proof.
reflexivity.
Qed.

Lemma slc_bind_abs : forall X Y (f : X -> SLC Y) (x : Derived_Mod SLC X),
  abs x >>= f = abs (x >>>= f).
Proof.
simpl. intros. f_equal.
apply slc_bind_fun_cong.
destruct u; simpl.
2: reflexivity.
unfold shift.
rewrite slc_fct_as_bind.
reflexivity.
Qed.

Remark lc_abs_hom : forall X Y (f : X -> LC Y) (x : Derived_Mod LC X),
  lc_abs (x >>>= f) = (lc_abs x : Taut_Mod LC _) >>>= f.
Proof.
simpl. intros. rewrite lc_bind_abs. f_equal.
apply lc_bind_fun_cong. destruct u; simpl. 2:reflexivity.
rewrite lc_fct_as_bind. reflexivity.
Qed.

Let abs_hom : Mod_Hom (Derived_Mod LC) LC :=
  Build_Mod_Hom (Derived_Mod LC) LC lc_abs lc_abs_hom.

Remark lc_app1_hom : forall X Y (f : X -> LC Y) (x : LC X),
  lc_app1 ((x : Taut_Mod LC X) >>>= f) =
    (lc_app1 x : Derived_Mod LC X) >>>= f.
Proof.
simpl. intros. rewrite <- lc_bind_app1.
apply lc_bind_fun_cong.
destruct u; simpl. 2:reflexivity.
rewrite lc_fct_as_bind. reflexivity.
Qed.

Let app1_hom : Mod_Hom LC (Derived_Mod LC) :=
  Build_Mod_Hom LC (Derived_Mod LC) lc_app1 lc_app1_hom.

Definition ELC : ExpMonad :=
  Build_ExpMonad abs_hom app1_hom lc_eta lc_beta.

Variable M : ExpMonad.

Fixpoint iota_fix X (x : term X) { struct x } : M X :=
  match x with
  | var a => unit M a
  | app x y =>
      exp_app M _ (iota_fix x) >>=
        default (@unit M X) (iota_fix y)
  | abs x => exp_abs M _ (iota_fix x)
  end.

Lemma iota_fix_unit : forall X (a : X),
  iota_fix (var a) = unit M a.
Proof.
reflexivity.
Qed.

Lemma iota_fix_fct : forall X Y (f : X -> Y) (x : term X),
  iota_fix (x //- f) = iota_fix x >>- f.
Proof.
intros. generalize Y f; clear Y f.
induction x; simpl; monad.
rewrite IHx1; clear IHx1.
rewrite IHx2; clear IHx2.
unfold map.
pose (mod_hom_mbind (exp_app M)). simpl in e. rewrite e.
rewrite bind_bind.
apply bind_congr. reflexivity.
destruct a; simpl; monad.
rewrite IHx; clear IHx.
pose (mod_hom_mbind (exp_abs M)). simpl in e. 
unfold map. rewrite <- e.
replace (iota_fix x >>= (fun x0 : option X => unit M (optmap f x0))) with
  (iota_fix x >>=
     default (fun u : X => unit M (f u) >>- Some (A:=Y)) (unit M None)).
reflexivity.
apply bind_congr. reflexivity.
destruct a; simpl; monad.
Qed.

Lemma iota_fix_bind : forall X Y (f : X -> term Y) (x : term X),
  iota_fix (x //= f) = iota_fix x >>= fun u => iota_fix (f u).
Proof.
intros. generalize Y f; clear Y f.
induction x; simpl; intros; monad.
rewrite IHx1; clear IHx1.
pose (mod_hom_mbind (exp_app M)). simpl in e. rewrite e.
rewrite bind_bind.
apply bind_congr. reflexivity.
destruct a; simpl. monad.
rewrite bind_unit. simpl. monad.
rewrite IHx.
pose (mod_hom_mbind (exp_abs M)). simpl in e. 
unfold map. rewrite <- e.
replace (iota_fix x >>= (fun u : option X => iota_fix (comm f u))) with
 (iota_fix x >>=
   default (fun u : X => iota_fix (f u) >>- Some (A:=Y)) (unit M None)).
reflexivity.
apply bind_congr. reflexivity.
destruct a; simpl.
unfold shift. rewrite iota_fix_fct. monad. reflexivity.
Qed.

Lemma iota_fix_app1 : forall X (x : term X),
  iota_fix (app1 x) = exp_app M X (iota_fix x).
Proof.
intros; rewrite app1_app; unfold shift; simpl.
rewrite iota_fix_fct.
unfold map.
pose (mod_hom_mbind (exp_app M)). simpl in e. rewrite e.
rewrite bind_bind.
apply unit_bind_match.
destruct a; simpl; monad.
Qed.

Lemma iota_fix_eta : forall X (x : term X),
  iota_fix (abs (app1 x)) = iota_fix x.
Proof.
intros. simpl.
rewrite iota_fix_app1.
rewrite exp_eta. reflexivity.
Qed.

Lemma iota_fix_beta : forall X (x : term (option X)) y,
  iota_fix (app (abs x) y) = iota_fix (x //= default (fun a => var a) y).
Proof.
intros; simpl.
rewrite exp_beta. rewrite iota_fix_bind.
apply bind_congr. reflexivity.
destruct a; simpl; reflexivity.
Qed.

Lemma iota_fix_wd : forall X (x y : term X),
  x == y -> iota_fix x = iota_fix y.
Proof.
induction 1.
auto.
simpl. rewrite IHlcr1. rewrite IHlcr2. reflexivity.
simpl. rewrite IHlcr. reflexivity.
destruct H.
apply iota_fix_beta.
apply iota_fix_eta.
auto.
eapply trans_eq; eauto.
Qed.

Let iota X : lc X -> M X :=
  lc_factor (@iota_fix X) (@iota_fix_wd X).

Remark iota_factorize : forall X (x : term X),
  iota (/ x) = iota_fix x.
Proof.
unfold iota. intros. rewrite lc_factorize. reflexivity.
Qed.

Opaque iota.

Remark iota_bind : forall X Y (f : X -> lc Y) (x : lc X),
  iota (lc_bind f x) = iota x >>= (fun a : X => iota (f a)).
Proof.
intros.
destruct (lc_class_surj x) as [y Hy]. subst x.
destruct (lc_fun_lift f) as [f' Hf]. subst f.
rewrite lc_bind_factorize.
do 2 rewrite iota_factorize.
rewrite iota_fix_bind.
apply bind_congr. reflexivity.
intro. rewrite iota_factorize. reflexivity.
Qed.

Remark iota_var : forall X (a : X),
  iota (lc_var a) = unit M a.
Proof.
simpl. unfold lc_var. intros.
rewrite iota_factorize. reflexivity.
Qed.

Lemma iota_app1 : forall X (x : lc X),
  iota (lc_app1 x) = exp_app M X (iota x).
Proof.
intros.
destruct (lc_class_surj x) as [y Hy]. subst x.
rewrite lc_app1_factorize.
do 2 rewrite iota_factorize.
rewrite iota_fix_app1. reflexivity.
Qed.

Lemma iota_abs : forall X (x : lc (option X)),
  iota (lc_abs x) = exp_abs M X (iota x).
Proof.
intros.
destruct (lc_class_surj x) as [y Hy]. subst x.
rewrite lc_abs_factorize.
do 2 rewrite iota_factorize. reflexivity.
Qed.

Let iota_monad : Monad_Hom LC M :=
  Build_Monad_Hom LC M iota iota_bind iota_var.

Let exp_iota : ExpMonad_Hom ELC M :=
  Build_ExpMonad_Hom ELC M iota_monad iota_app1 iota_abs.

Theorem iota_unique : forall (j : ExpMonad_Hom ELC M) X (x : lc X),
  j X x = exp_iota X x.
Proof.
intros. destruct j as [[p p_bind p_var] p_app p_abs].
simpl in *. unfold lc_var in *.
destruct (lc_class_surj x) as [y Hy]. subst x.
rewrite iota_factorize.
induction y.
simpl. auto.
rewrite app_as_app1. rewrite iota_fix_bind.
rewrite iota_fix_app1. rewrite <- lc_bind_factorize.
rewrite p_bind. rewrite <- lc_app1_factorize.
rewrite p_app. rewrite IHy1.
apply bind_congr. reflexivity.
destruct a; simpl; auto.
simpl. rewrite <- lc_abs_factorize. rewrite p_abs.
replace (p (option X) (/ y)) with (iota_fix y).
reflexivity.
Qed.

End Lc_exp.
