Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.
Require Import StructTact.FilterMap.
Require Import StructTact.RemoveAll.

Set Implicit Arguments.

Fixpoint subseq {A} (xs ys : list A) : Prop :=
  match xs, ys with
    | [], _ => True
    | x :: xs', y :: ys' => (x = y /\ subseq xs' ys') \/ subseq xs ys'
    | _, _ => False
  end.

Lemma subseq_refl : forall A (l : list A), subseq l l.
Proof.
  induction l; simpl; tauto.
Qed.

Lemma subseq_trans :
  forall A (zs xs ys : list A),
    subseq xs ys ->
    subseq ys zs ->
    subseq xs zs.
Proof.
  induction zs; intros; simpl in *;
  repeat break_match; subst; simpl in *; intuition; subst; eauto;
  right; (eapply IHzs; [|eauto]); simpl; eauto.
Qed.

Lemma subseq_In :
  forall A (ys xs : list A) x,
    subseq xs ys ->
    In x xs ->
    In x ys.
Proof.
  induction ys; intros.
  - destruct xs; simpl in *; intuition.
  - simpl in *. break_match; simpl in *; intuition; subst; intuition eauto;
                right; (eapply IHys; [eauto| intuition]).
Qed.

Theorem subseq_NoDup :
  forall A (ys xs : list A),
    subseq xs ys ->
    NoDup ys ->
    NoDup xs.
Proof.
  induction ys; intros.
  - destruct xs; simpl in *; intuition.
  - simpl in *. invc_NoDup.
    break_match.
    + constructor.
    + intuition.
      subst. constructor; eauto using subseq_In.
Qed.

Lemma subseq_remove :
  forall A A_eq_dec (x : A) xs,
    subseq (remove A_eq_dec x xs) xs.
Proof.
  induction xs; intros; simpl.
  - auto.
  - repeat break_match; auto.
    + intuition congruence.
    + find_inversion. auto.
Qed.

Lemma subseq_map :
  forall A B (f : A -> B) ys xs,
    subseq xs ys ->
    subseq (map f xs) (map f ys).
Proof.
  induction ys; intros; simpl in *.
  - repeat break_match; try discriminate; auto.
  - repeat break_match; try discriminate; auto.
    intuition.
    + subst. simpl in *. find_inversion. auto.
    + right. repeat find_reverse_rewrite. auto.
Qed.

Lemma subseq_cons_drop :
  forall A xs ys (a : A),
    subseq (a :: xs) ys -> subseq xs ys.
Proof.
  induction ys; intros; simpl in *; intuition; break_match; eauto.
Qed.

Lemma subseq_length :
  forall A (ys xs : list A),
    subseq xs ys ->
    length xs <= length ys.
Proof.
  induction ys; intros; simpl in *; break_match; intuition.
  subst. simpl in *. specialize (IHys l). concludes. auto with *.
Qed.

Lemma subseq_subseq_eq :
  forall A (xs ys : list A),
    subseq xs ys ->
    subseq ys xs ->
    xs = ys.
Proof.
  induction xs; intros; destruct ys; simpl in *;
    intuition eauto using f_equal2, subseq_cons_drop.
  exfalso.
  repeat find_apply_lem_hyp subseq_length.
  simpl in *. omega.
Qed.

Lemma subseq_filter :
  forall A (f : A -> bool) xs,
    subseq (filter f xs) xs.
Proof.
  induction xs; intros; simpl.
  - auto.
  - repeat break_match; intuition congruence.
Qed.

Lemma subseq_nil :
  forall A xs,
    subseq (A:=A) [] xs.
Proof.
  destruct xs; simpl; auto.
Qed.

Lemma subseq_skip :
  forall A a xs ys,
    subseq(A:=A) xs ys ->
    subseq xs (a :: ys).
Proof.
  induction ys; intros; simpl in *; repeat break_match; intuition.
Qed.

Lemma subseq_filterMap :
  forall A B (f : A -> option B) ys xs,
    subseq xs ys ->
    subseq (filterMap f xs) (filterMap f ys).
Proof.
  induction ys; intros; simpl in *; repeat break_match; auto; try discriminate; intuition; subst.
  - simpl. find_rewrite. auto.
  - auto using subseq_skip.
  - auto using subseq_nil.
  - simpl. find_rewrite. auto.
Qed.

Lemma subseq_app_r :
  forall A xs ys,
    subseq (A:=A) ys (xs ++ ys).
Proof.
  induction xs; intros; simpl.
  + auto using subseq_refl.
  + break_match.
    * auto.
    * right. auto using subseq_nil.
Qed.

Lemma subseq_app_tail :
  forall A ys xs zs,
    subseq (A:=A) xs ys ->
    subseq (xs ++ zs) (ys ++ zs).
Proof.
  induction ys; intros; simpl in *.
  - break_match; intuition auto using subseq_refl.
  - repeat break_match.
    + auto.
    + discriminate.
    + simpl in *. subst. right. auto using subseq_app_r.
    + simpl in *. find_inversion. intuition.
      rewrite app_comm_cons. auto.
Qed.

Lemma subseq_app_head :
  forall A xs ys zs,
    subseq (A:=A) ys zs ->
    subseq (A:=A) (xs ++ ys) (xs ++ zs).
Proof.
  induction xs; intros; simpl; intuition.
Qed.

Lemma subseq_2_3 :
  forall A xs ys zs x y,
    subseq(A:=A) (xs ++ ys ++ zs) (xs ++ x :: ys ++ y :: zs).
Proof.
  auto using subseq_refl, subseq_skip, subseq_app_head.
Qed.

Lemma subseq_middle :
  forall A xs y zs,
    subseq (A:=A) (xs ++ zs) (xs ++ y :: zs).
Proof.
  intros.
  apply subseq_app_head.
  apply subseq_skip.
  apply subseq_refl.
Qed.

Lemma subseq_remove_all :
  forall A A_eq_dec (ds l l' : list A),
    subseq l l' ->
    subseq (remove_all A_eq_dec ds l) l'.
Proof.
  induction ds; intros; simpl.
  - auto.
  - apply IHds.
    eapply subseq_trans.
    apply subseq_remove.
    auto.
Qed.
