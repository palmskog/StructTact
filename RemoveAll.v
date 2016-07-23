Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import StructTact.StructTactics.
Require Import StructTact.Dedup.
Require Import StructTact.Before.

Set Implicit Arguments.

Section remove_all.
  Variable (A : Type).
  Hypothesis (A_eq_dec : forall x y : A, {x = y} + {x <> y}).

  Fixpoint remove_all (to_delete l : list A) : list A :=
    match to_delete with
      | [] => l
      | d :: ds => remove_all ds (remove A_eq_dec d l)
    end.

  Lemma in_remove_all_was_in :
    forall ds l x,
      In x (remove_all ds l) ->
      In x l.
  Proof.
    induction ds; intros; simpl in *; intuition.
    eauto using in_remove.
  Qed.

  Lemma in_remove_all_preserve :
    forall ds l x,
      ~ In x ds ->
      In x l ->
      In x (remove_all ds l).
  Proof.
    induction ds; intros; simpl in *; intuition auto using remove_preserve.
  Qed.
End remove_all.
Arguments in_remove_all_was_in : clear implicits.

Lemma in_remove_all_not_in :
  forall A A_eq_dec ds l x,
    In x (remove_all (A:=A) A_eq_dec ds l) ->
    In x ds ->
    False.
Proof.
  induction ds; intros; simpl in *; intuition.
  - subst. find_apply_lem_hyp in_remove_all_was_in.
    eapply remove_In; eauto.
  - eauto.
Qed.

Lemma remove_all_nil :
  forall A dec ys,
    remove_all (A := A) dec ys [] = [].
Proof.
  intros. induction ys; simpl in *; intuition.
Qed.

Lemma remove_all_cons :
  forall A dec ys a l,
    (remove_all (A := A) dec ys (a :: l) = remove_all dec ys l /\
     In a ys) \/
    (remove_all (A := A) dec ys (a :: l) = a :: (remove_all dec ys l) /\
     ~In a ys).
Proof.
  induction ys; intros; simpl in *; intuition.
  break_if; subst; simpl in *; intuition.
  specialize (IHys a0 (remove dec a l)). intuition.
Qed.

Lemma before_remove_all :
  forall A x y l ys dec,
    before (A := A) x y (remove_all dec ys l) ->
    ~ In y ys ->
    before x y l.
Proof.
  induction l; intros; simpl in *; intuition.
  - rewrite remove_all_nil in *. simpl in *. intuition.
  - pose proof remove_all_cons dec ys a l. intuition.
    + repeat find_rewrite. right. intuition eauto.
      subst; intuition.
    + repeat find_rewrite. simpl in *. intuition eauto.
Qed.

Lemma before_remove_all_if :
  forall A x y l xs dec,
    before x y l ->
    ~ In x xs ->
    before (A := A) x y (remove_all dec xs l).
Proof.
  induction l; intros; simpl in *; intuition;
  pose proof remove_all_cons dec xs a l; subst; intuition;
  repeat find_rewrite; simpl in *; intuition.
Qed.
