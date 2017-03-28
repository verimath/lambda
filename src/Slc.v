(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(** *  Syntactic Lambda calculus *)

(** Lambda terms modulo alpha-equivalence (and its monadic
    structure given by the substitution). *)

Set Implicit Arguments.

Require Export Misc.

(** ** Notations *)

Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x == y :> X"
  (at level 70, y at next level, no associativity).

Reserved Notation "x //= f" (at level 42, left associativity).
Reserved Notation "x //- f" (at level 42, left associativity).

Implicit Type X Y Z : Set.

(** ** Inductive datatype of terms *)

Inductive term (X : Set) : Set :=
  | var : X -> term X
  | app : term X -> term X -> term X
  | abs : term (option X) -> term X.

Hint Extern 1 (_ = _ :> term _) => autorewrite with slc; simpl : slc.

Fixpoint fct X Y (f : X -> Y) (x : term X) { struct x } : term Y :=
  match x with
  | var a => var (f a)
  | app x y => app (x //- f) (y //- f)
  | abs x => abs (x //- optmap f)
  end
where "x //- f" := (@fct _ _ f x).

Lemma fct_fun_cong :
  forall X (x : term X) Y (f g : X -> Y),
  (forall u, f u = g u) -> x //- f = x //- g.
Proof.
induction x; simpl; auto.
intros. f_equal. apply IHx.
destruct u; simpl; auto.
Qed.

Lemma fct_fct :
  forall X Y Z (f : X -> Y) (g : Y -> Z) (x : term X) ,
  x //- f //- g = x //- (fun u => g (f u)).
Proof.
intros. generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; auto.
f_equal. rewrite IHx.
apply fct_fun_cong. destruct u; reflexivity.
Qed.
Hint Rewrite fct_fct : slc.

Lemma fct_id : forall X (f : X -> X) (x : term X),
  (forall u, f u = u) -> x //- f = x.
Proof.
induction x; intros; simpl; f_equal; auto.
apply IHx.
destruct u; simpl; auto.
Qed.

Definition shift X (x : term X) : term (option X) :=
  x //- @Some X.

Lemma shift_fct : forall X Y (f : X -> Y) (x : term X),
  shift (x //- f) = x //- fun a => Some (f a).
Proof.
unfold shift. intros. rewrite fct_fct. reflexivity.
Qed.

Lemma fct_shift : forall X Y (f : option X -> Y) (x : term X),
  shift x //- f = x //- fun a => f (Some a).
Proof.
unfold shift. intros. rewrite fct_fct. reflexivity.
Qed.

Hint Rewrite shift_fct fct_shift : slc.

Definition comm
  (X Y : Set) (f : X -> term Y) (x : option X) : term (option Y) :=
  match x with
  | Some a => shift (f a)
  | None => var None
  end.

Remark comm_var : forall X (u : option X), comm (@var X) u = var u.
Proof.
destruct u; reflexivity.
Qed.

Fixpoint slc_bind X Y (f : X -> term Y) (x : term X) { struct x } : term Y :=
  match x with
  | var x => f x
  | app x y => app (x //= f) (y //= f)
  | abs x => abs (x //= comm f)
  end
where "x //= f" := (@slc_bind _ _ f x).

Ltac slc :=
  intros;
  repeat first [ progress simpl fct
               | progress simpl slc_bind
               | progress autorewrite with slc ];
  auto with slc.

Lemma slc_bind_fun_cong : forall X (x : term X) Y (f g : X -> term Y),
  (forall u, f u = g u) -> x //= f = x //= g.
Proof.
induction x; simpl; intros; auto.
f_equal. apply IHx.
destruct u; simpl; auto.
Qed.

Lemma slc_bind_var : forall X Y (f : X -> term Y) (x : X),
  var x //=  f = f x.
Proof.
reflexivity.
Qed.

Lemma slc_var_bind_match : forall X (x : term X) (f : X -> term X),
  (forall u, f u = var u) -> x //= f = x.
Proof.
induction x; simpl; intros; auto.
f_equal. apply IHx.
destruct u; simpl. rewrite H. reflexivity. reflexivity.
Qed.
Hint Resolve slc_var_bind_match : slc.

Lemma slc_var_bind : forall X (x : term X),
  x //= @var X = x.
Proof.
intros. apply slc_var_bind_match. reflexivity.
Qed.

Lemma slc_fct_bind : forall X Y Z (f : X -> term Y) (g : Y -> Z) (x : term X),
  x //= f //- g = x //= fun u => f u //- g.
Proof.
intros. generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; f_equal; auto.
rewrite IHx.
apply slc_bind_fun_cong.
destruct u; slc.
Qed.
Hint Rewrite slc_fct_bind : slc.

Lemma slc_bind_fct : forall X Y Z (f : X -> Y) (g : Y -> term Z) (x : term X),
  x //- f //= g = x //= fun u => g (f u).
Proof.
intros; generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; f_equal; auto.
rewrite IHx.
apply slc_bind_fun_cong. clear x IHx.
destruct u; reflexivity.
Qed.
Hint Rewrite slc_bind_fct : slc.

Lemma slc_shift_bind : forall X Y (f : X -> term Y) (x : term X),
  shift (x //= f) = x //= fun a => shift (f a).
Proof.
unfold shift. intros.
rewrite slc_fct_bind. reflexivity.
Qed.

Lemma slc_bind_shift : forall X Y (f : option X -> term Y) (x : term X),
  shift x //= f = x //= fun a => f (Some a).
Proof.
unfold shift. intros.
rewrite slc_bind_fct. reflexivity.
Qed.

Hint Rewrite slc_shift_bind slc_bind_shift : slc.

Lemma slc_bind_bind : forall X Y Z
  (f : X -> term Y) (g : Y -> term Z) (x : term X),
  x //= f //= g = x //= fun u => f u //= g.
Proof.
intros. generalize Y Z f g; clear Y Z f g.
induction x; simpl; intros; f_equal; auto.
rewrite IHx.
apply slc_bind_fun_cong.
clear x IHx. destruct u; slc.
Qed.
Hint Rewrite slc_bind_bind : slc.

Lemma slc_fct_as_bind : forall X Y (f : X -> Y) (x : term X),
  x //- f = x //= (fun a => var (f a)).
Proof.
intros. generalize Y f; clear Y f.
induction x; simpl; intros; auto.
rewrite IHx; clear IHx.
f_equal. apply slc_bind_fun_cong.
destruct u; reflexivity.
Qed.

Definition app1 X (x : term X) : term (option X) :=
  app (shift x) (var None).

Lemma app1_app : forall X (x : term X),
  app1 x = app (shift x) (var None).
Proof.
reflexivity.
Qed.

Opaque app1.

Lemma fct_app1 : forall X Y (f : X -> Y) (x : term X),
  app1 x //- (optmap f) = app1 (x //- f).
Proof.
intros.
do 2 rewrite app1_app.
simpl. slc.
Qed.
Hint Rewrite fct_app1 : slc.

Lemma app_as_app1 : forall X (x y : term X),
  app x y = app1 x //= default (@var _) y.
Proof.
intros. rewrite app1_app. slc.
symmetry. slc.
Qed.

Lemma slc_bind_app1 : forall X Y (f : option X -> term Y) (x : term X),
  app1 x //= f = app (x //= fun u : X => f (Some u)) (f None).
Proof.
intros. rewrite app1_app. simpl. slc.
Qed.

Hint Rewrite slc_bind_app1 : slc.

Inductive Beta X : term X -> term X -> Prop :=
  | beta_intro : forall (x1 : term (option X)) (x2 : term X),
      Beta (app (abs x1) x2) (x1 //= (default (fun a => var a) x2)).

Lemma beta_intro_alt : forall X (x1 : term (option X)) (x2 y : term X),
  x1 //= (default (fun a => var a) x2) = y -> Beta (app (abs x1) x2) y.
Proof.
intros. subst y. apply beta_intro.
Qed.

Inductive lcr (X : Set) : term X -> term X -> Prop :=
  | lcr_var : forall a : X, var a == var a
  | lcr_app : forall x1 x2 y1 y2 : term X,
      x1 == x2 -> y1 == y2 -> app x1 y1 == app x2 y2
  | lcr_abs : forall x y : term (option X), x == y -> abs x == abs y
  | lcr_beta : forall x y : term X, Beta x y -> x == y
  | lcr_eta : forall x : term X, abs (app1 x) == x
  | lcr_sym : forall x y : term X, y == x -> x == y
  | lcr_trs : forall x y z : term X, lcr x y -> lcr y z -> lcr x z
where "x == y" := (@lcr _ x y).

Hint Resolve lcr_var lcr_app lcr_abs lcr_eta lcr_beta lcr_trs : slc.
Hint Immediate lcr_sym : slc.

Lemma lcr_rfl : forall X (x : term X), x == x.
Proof.
induction x; constructor; auto.
Qed.
Hint Resolve lcr_rfl : slc.

Lemma lcr_eq : forall X (x y : term X), x = y -> x == y.
Proof.
intros; subst y; slc.
Qed.
Hint Resolve lcr_eq : slc.

Lemma eta_fct : forall X Y (f : X -> Y) (x : term X),
  abs (app1 x) //- f = abs (app1 (x //- f)).
Proof.
induction x; simpl; slc.
Qed.

Lemma lcr_fct : forall X Y (f : X -> Y) (x y : term X),
  x == y -> x //- f == y //- f.
Proof.
intros. generalize Y f. clear Y f.
induction H; intros; try solve [simpl; slc].
2: eauto with slc.
destruct H.
simpl. slc.
apply lcr_beta. apply beta_intro_alt.
slc.
apply slc_bind_fun_cong.
destruct u; reflexivity.
Qed.

Hint Resolve lcr_fct : slc.

Lemma slc_eta_bind : forall X Y (f : X -> term Y) (x : term X),
  abs (app1 x) //= f = abs (app1 (x //= f)).
Proof.
intros. simpl. slc.
rewrite app1_app. slc.
Qed.

Lemma lcr_bind_arg : forall X Y (f : X -> term Y) (x y : term X),
  x == y -> x //= f == y //= f.
Proof.
intros. generalize Y f; clear Y f.
induction H; intros; try solve [simpl; slc].
3: eauto with slc.
2: rewrite slc_eta_bind; slc.
destruct H. simpl.
rewrite slc_bind_bind.
apply lcr_beta.
apply beta_intro_alt.
rewrite slc_bind_bind.
apply slc_bind_fun_cong.
destruct u; simpl; slc.
Qed.

Lemma lcr_bind_fun : forall X Y  (f g : X -> term Y) (x : term X),
  (forall u, f u == g u) -> x //= f == x //= g.
Proof.
intros. generalize Y f g H; clear Y f g H.
induction x; intros; simpl; slc.
apply lcr_abs.
apply IHx.
destruct u; simpl; unfold shift; slc.
Qed.

Lemma lcr_bind : forall X Y (f g : X -> term Y) (x y : term X),
  (forall u, f u == g u) -> x == y -> x //= f == y //= g.
Proof.
intros.
apply lcr_trs with (x //= g).
apply lcr_bind_fun; assumption.
apply lcr_bind_arg; assumption.
Qed.

Lemma lcr_app1 : forall X (x y : term X),
  x == y -> app1 x == app1 y.
Proof.
intros. do 2 rewrite app1_app. unfold shift. slc.
Qed.
