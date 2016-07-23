Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import StructTact.StructTactics.

Set Implicit Arguments.

Fixpoint before {A: Type} (x : A) y l : Prop :=
  match l with
    | [] => False
    | a :: l' =>
      a = x \/
      (a <> y /\ before x y l')
  end.

Lemma before_In :
  forall A x y l,
    before (A:=A) x y l ->
    In x l.
Proof.
  induction l; intros; simpl in *; intuition.
Qed.

Lemma before_split :
  forall A l (x y : A),
    before x y l ->
    x <> y ->
    In x l ->
    In y l ->
    exists xs ys zs,
      l = xs ++ x :: ys ++ y :: zs.
Proof.
  induction l; intros; simpl in *; intuition; subst; try congruence.
  - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
  - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
  - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
  - eapply_prop_hyp In In; eauto. break_exists. subst.
    exists (a :: x0), x1, x2. auto.
Qed.

Lemma In_app_before :
  forall A xs ys x y,
    In(A:=A) x xs ->
    (~ In y xs) ->
    before x y (xs ++ y :: ys).
Proof.
  induction xs; intros; simpl in *; intuition.
Qed.

Fixpoint before_func {A: Type} (f : A -> bool) (g : A -> bool) (l : list A) : Prop :=
  match l with
    | [] => False
    | a :: l' =>
      f a = true \/
      (g a = false /\ before_func f g l')
  end.

Definition before_func_dec :
  forall A f g (l : list A),
    {before_func f g l} + {~ before_func f g l}.
Proof.
  intros. induction l; simpl in *.
  - intuition.
  - destruct (f a); destruct (g a); intuition.
Qed.

Lemma before_func_app :
  forall A f g l x,
    before_func (A := A) f g l ->
    before_func f g (l ++ x).
Proof.
  intros. induction l; simpl in *; intuition.
Qed.

Lemma before_2_3_insert :
  forall A xs ys zs x y a b,
    before(A:=A) a b (xs ++ ys ++ zs) ->
    b <> x ->
    b <> y ->
    before a b (xs ++ x :: ys ++ y :: zs).
Proof.
  induction xs; intros; simpl in *; intuition.
  induction ys; intros; simpl in *; intuition.
Qed.

Lemma before_middle_insert :
  forall A xs y zs a b,
    before(A:=A) a b (xs ++ zs) ->
    b <> y ->
    before a b (xs ++ y :: zs).
Proof.
  intros.
  induction xs; intros; simpl in *; intuition.
Qed.

Lemma before_2_3_reduce :
  forall A xs ys zs x y a b,
    before(A:=A) a b (xs ++ x :: ys ++ y :: zs) ->
    a <> x ->
    a <> y ->
    before a b (xs ++ ys ++ zs).
Proof.
  induction xs; intros; simpl in *; intuition; try congruence; eauto.
  induction ys; intros; simpl in *; intuition; try congruence.
Qed.

Lemma before_middle_reduce :
  forall A xs zs a b y,
    before(A:=A) a b (xs ++ y :: zs) ->
    a <> y ->
    before a b (xs ++ zs).
Proof.
  induction xs; intros; simpl in *; intuition; try congruence; eauto.
Qed.

Lemma before_remove :
  forall A x y l y' dec,
    before (A := A) x y (remove dec y' l) ->
    y <> y' ->
    before x y l.
Proof.
  induction l; intros; simpl in *; intuition.
  break_if; subst; simpl in *; intuition eauto.
Qed.

Lemma before_remove_if :
  forall A (x : A) y l x' dec,
    before x y l ->
    x <> x' ->
    before x y (remove dec x' l).
Proof.
  induction l; intros; simpl in *; intuition;
  break_if; subst; simpl in *; intuition eauto.
Qed.

Lemma before_app :
  forall A x y l' l,
    before (A := A) x y (l' ++ l) ->
    ~ In x l' ->
    before (A := A) x y l.
Proof.
  induction l'; intros; simpl in *; intuition.
Qed.

Lemma before_app_if :
  forall A x y l' l,
    before (A := A) x y l ->
    ~ In y l' ->
    before (A := A) x y (l' ++ l).
Proof.
  induction l'; intros; simpl in *; intuition.
Qed.

Lemma before_antisymmetric :
  forall A x y l,
    before (A := A) x y l ->
    before y x l ->
    x = y.
Proof.
  intros.
  induction l; simpl in *; intuition; congruence.
Qed.
