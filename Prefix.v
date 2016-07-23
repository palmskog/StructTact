Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import StructTact.StructTactics.

Fixpoint Prefix {A} (l1 : list A) l2 : Prop :=
  match l1, l2 with
    | a :: l1', b :: l2' => a = b /\ Prefix l1' l2'
    | [], _ => True
    | _, _ => False
  end.

Lemma Prefix_nil :
  forall A (l : list A),
    Prefix l [] ->
    l = [].
Proof.
  intros. destruct l.
  - reflexivity.
  - contradiction.
Qed.

Lemma Prefix_cons :
  forall A (l l' : list A) a,
    Prefix l' l ->
    Prefix (a :: l') (a :: l).
Proof.
  simpl. intuition.
Qed.

Lemma Prefix_in :
  forall A (l l' : list A),
    Prefix l' l ->
    (forall x, In x l' -> In x l).
Proof.
  induction l; intros l' H.
  - find_apply_lem_hyp Prefix_nil. subst. contradiction.
  - destruct l'.
    + contradiction.
    + intros. simpl Prefix in *. break_and. subst. simpl in *. intuition.
      right. eapply IHl; eauto.
Qed.

Lemma app_Prefix :
  forall A (xs ys zs : list A),
    xs ++ ys = zs ->
    Prefix xs zs.
Proof.
  induction xs; intros; simpl in *.
  - auto.
  - break_match.
    + discriminate.
    + subst. find_inversion. eauto.
Qed.

Lemma Prefix_In :
  forall A (l : list A) l' x,
    Prefix l l' ->
    In x l ->
    In x l'.
Proof.
  induction l; intros; simpl in *; intuition;
  subst; break_match; intuition; subst; intuition.
Qed.
