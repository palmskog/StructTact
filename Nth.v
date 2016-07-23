Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import StructTact.StructTactics.
Require Import StructTact.ListUtil.

Inductive Nth {A : Type} : list A -> nat -> A -> Prop :=
| Nth_0 : forall x l, Nth (x :: l) 0 x
| Nth_S : forall l x n y, Nth l n x -> Nth (y :: l) (S n) x.

Lemma nth_error_Nth :
  forall A n l (x : A),
    nth_error l n = Some x ->
    Nth l n x.
Proof.
  induction n; intros; simpl in *; auto.
  - break_match; try discriminate.
    unfold value in *.
    find_inversion.
    constructor.
  - break_match; try discriminate.
    subst. constructor.
    eauto.
Qed.

Lemma Nth_nth_error :
  forall A n l (x : A),
    Nth l n x ->
    nth_error l n = Some x.
Proof.
  intros.
  induction H; simpl in *; auto.
Qed.
