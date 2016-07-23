Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.
Require Import StructTact.Dedup.

Set Implicit Arguments.

Notation member := (in_dec eq_nat_dec).

Lemma filter_app : forall A (f : A -> bool) xs ys,
    filter f (xs ++ ys) = filter f xs ++ filter f ys.
Proof.
  induction xs; intros.
  - auto.
  - simpl. rewrite IHxs. break_if; auto.
Qed.

Lemma filter_fun_ext_eq : forall A f g xs,
                            (forall a : A, In a xs -> f a = g a) ->
                            filter f xs = filter g xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl. rewrite H by intuition. rewrite IHxs by intuition. auto.
Qed.

Lemma NoDup_map_injective : forall A B (f : A -> B) xs,
                              (forall x y, In x xs -> In y xs ->
                                           f x = f y -> x = y) ->
                              NoDup xs -> NoDup (map f xs).
Proof.
  induction xs; intros.
  - constructor.
  - simpl. invc_NoDup. constructor.
    + intro. do_in_map.
      assert (x = a) by intuition.
      congruence.
    + intuition.
Qed.

Lemma NoDup_disjoint_append :
  forall A (l : list A) l',
    NoDup l ->
    NoDup l' ->
    (forall a, In a l -> ~ In a l') ->
    NoDup (l ++ l').
Proof.
  induction l; intros.
  - auto.
  - simpl. invc_NoDup. constructor.
    + intro. do_in_app. intuition eauto with *.
    + intuition eauto with *.
Qed.

Lemma filter_NoDup :
  forall A p (l : list A),
    NoDup l ->
    NoDup (filter p l).
Proof.
  induction l; intros.
  - auto.
  - invc_NoDup. simpl. break_if; auto.
    constructor; auto.
    intro. apply filter_In in H. intuition.
Qed.


Lemma NoDup_map_filter :
  forall A B (f : A -> B) g l,
    NoDup (map f l) ->
    NoDup (map f (filter g l)).
Proof.
  intros. induction l; simpl in *.
  - constructor.
  - invc_NoDup. concludes.
    break_if; simpl in *; auto.
    constructor; auto.
    intro. do_in_map.
    find_apply_lem_hyp filter_In. intuition.
    match goal with | H : _ -> False |- False => apply H end.
    apply in_map_iff. eauto.
Qed.


Lemma filter_true_id : forall A (f : A -> bool) xs,
                         (forall x, In x xs -> f x = true) ->
                         filter f xs = xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl. now rewrite H, IHxs by intuition.
Qed.

Lemma map_of_map : forall A B C (f : A -> B) (g : B -> C) xs,
                     map g (map f xs) = map (fun x => g (f x)) xs.
Proof.
  induction xs; simpl; auto using f_equal2.
Qed.

Lemma filter_except_one : forall A A_eq_dec (f g : A -> bool) x xs,
                            (forall y, In y xs ->
                                       x <> y ->
                                       f y = g y) ->
                            g x = false ->
                            filter f (remove A_eq_dec x xs) = filter g xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl.
    break_if.
    + subst. repeat find_rewrite. eauto with *.
    + simpl. rewrite H by auto with *.
      break_if; eauto using f_equal2 with *.
Qed.

Lemma flat_map_nil : forall A B (f : A -> list B) l,
                       flat_map f l = [] ->
                       l = [] \/ (forall x, In x l -> f x = []).
Proof.
  induction l; intros.
  - intuition.
  - right. simpl in *.
    apply app_eq_nil in H.
    intuition; subst; simpl in *; intuition.
Qed.

Fixpoint remove_first {A : Set} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : list A :=
  match l with
    | [] => []
    | y::tl => if (A_eq_dec x y) then tl else y::(remove_first A_eq_dec x tl)
  end.

Theorem NoDup_Permutation_NoDup :
  forall A (l l' : list A),
    NoDup l ->
    Permutation l l' ->
    NoDup l'.
Proof.
  intros A l l' Hnd Hp.
  induction Hp; auto; invc_NoDup; constructor;
    eauto using Permutation_in, Permutation_sym;
    simpl in *; intuition.
Qed.

Theorem NoDup_append :
  forall A l (a : A),
    NoDup (l ++ [a]) <-> NoDup (a :: l).
Proof.
  intuition eauto using NoDup_Permutation_NoDup, Permutation_sym, Permutation_cons_append.
Qed.

Lemma NoDup_map_elim :
  forall A B (f : A -> B) xs x y,
    f x = f y ->
    NoDup (map f xs) ->
    In x xs ->
    In y xs ->
    x = y.
Proof.
  induction xs; intros; simpl in *.
  - intuition.
  - invc_NoDup. intuition; subst; auto; exfalso.
    + repeat find_rewrite. auto using in_map.
    + repeat find_reverse_rewrite. auto using in_map.
Qed.

Lemma remove_length_not_in : forall A A_eq_dec (x : A) xs,
                               ~ In x xs ->
                               length (remove A_eq_dec x xs) = length xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl in *. intuition.
    break_if; subst; simpl; intuition.
Qed.

Lemma remove_length_in : forall A A_eq_dec (x : A) xs,
                           In x xs ->
                           NoDup xs ->
                           S (length (remove A_eq_dec x xs)) = length xs.
Proof.
  induction xs; intros; simpl in *; intuition; invc_NoDup;
    break_if; subst; intuition (simpl; try congruence).
  now rewrite remove_length_not_in.
Qed.


Lemma subset_size_eq :
  forall A xs,
    NoDup xs ->
    forall ys,
      NoDup ys ->
      (forall x : A, In x xs -> In x ys) ->
      length xs = length ys ->
      (forall x, In x ys -> In x xs).
Proof.
  induction xs; intros.
  - destruct ys; simpl in *; congruence.
  - invc_NoDup. concludes.
    assert (In a ys) by eauto with *.

    find_apply_lem_hyp in_split.
    break_exists_name l1.
    break_exists_name l2.
    subst.

    specialize (IHxs (l1 ++ l2)).

    conclude_using ltac:(eauto using NoDup_remove_1).

    forward IHxs.
    intros x' Hx'.
    assert (In x' (l1 ++ a :: l2)) by eauto with *.
    do_in_app. simpl in *. intuition. subst. congruence.
    concludes.

    forward IHxs.
    rewrite app_length in *. simpl in *. omega.
    concludes.

    do_in_app. simpl in *. intuition.
Qed.

Lemma remove_NoDup :
  forall A A_eq_dec (x : A) xs,
    NoDup xs ->
    NoDup (remove A_eq_dec x xs).
Proof.
  induction xs; intros.
  - auto with struct_util.
  - invc_NoDup. simpl. break_if; eauto 6 using in_remove with struct_util.
Qed.

Lemma seq_range :
  forall n a x,
    In x (seq a n) ->
    a <= x < a + n.
Proof.
  induction n; intros; simpl in *.
  - intuition.
  - break_or_hyp; try find_apply_hyp_hyp; intuition.
Qed.


Lemma seq_NoDup : forall n a ,
                    NoDup (seq a n).
Proof.
  induction n; intros; simpl in *; constructor; auto.
  intro. apply seq_range in H. omega.
Qed.

Lemma remove_length_ge : forall A A_eq_dec (x : A) xs,
                           NoDup xs ->
                           length (remove A_eq_dec x xs) >= length xs - 1.
Proof.
  induction xs; intros.
  - auto.
  - invc_NoDup. simpl. break_if.
    + rewrite <- minus_n_O.
      subst.
      rewrite remove_length_not_in; auto.
    + simpl. concludes. omega.
Qed.

Lemma remove_length_le :
  forall A (x : A) xs eq_dec,
    length xs >= length (remove eq_dec x xs).
Proof.
  induction xs; intros.
  - auto.
  - simpl in *.
    specialize (IHxs eq_dec).
    break_if; subst; simpl; omega.
Qed.

Lemma remove_length_lt :
  forall A (x : A) xs eq_dec,
    In x xs ->
    length xs > length (remove eq_dec x xs).
Proof.
  induction xs; intros; simpl in *; intuition.
  - subst.
    break_if; try congruence.
    pose proof remove_length_le x xs eq_dec.
    omega.
  - specialize (IHxs ltac:(eauto) ltac:(eauto)).
    break_if; subst; simpl; omega.
Qed.

Lemma subset_length :
  forall A xs ys,
    (forall a b : A, {a = b} + {a <> b}) ->
    NoDup xs ->
    (forall x : A, In x xs -> In x ys) ->
    length ys >= length xs.
Proof.
  induction xs; intros.
  - simpl. omega.
  - specialize (IHxs (remove X a ys) X).
    invc_NoDup.
    concludes.

    forward IHxs.
    intros.
    apply remove_preserve; [congruence|intuition].
    concludes.

    pose proof remove_length_lt a ys X.
    conclude_using intuition.

    simpl. omega.
Qed.

Lemma app_cons_singleton_inv :
  forall A xs (y : A) zs w,
    xs ++ y :: zs = [w] ->
    xs = [] /\ y = w /\ zs = [].
Proof.
  intros.
  destruct xs.
  - solve_by_inversion.
  - destruct xs; solve_by_inversion.
Qed.


Lemma app_cons_in :
  forall A (l : list A) xs a ys,
    l = xs ++ a :: ys ->
    In a l.
Proof.
  intros. subst. auto with *.
Qed.
Hint Resolve app_cons_in : struct_util.

Lemma app_cons_in_rest:
  forall A (l : list A) xs a b ys,
    l = xs ++ a :: ys ->
    In b (xs ++ ys) ->
    In b l.
Proof.
  intros. subst. in_crush.
Qed.
Hint Resolve app_cons_in_rest : struct_util.

Lemma remove_filter_commute :
  forall A  (l : list A) A_eq_dec f x,
    remove A_eq_dec x (filter f l) = filter f (remove A_eq_dec x l).
Proof.
  induction l; intros; simpl in *; auto.
  repeat (break_if; subst; simpl in *; try congruence).
Qed.

Lemma In_filter_In :
  forall A (f : A -> bool) x l l',
    filter f l = l' ->
    In x l' -> In x l.
Proof.
  intros. subst.
  eapply filter_In; eauto.
Qed.

Lemma filter_partition :
  forall A (l1 : list A) f l2 x l1' l2',
    NoDup (l1 ++ x :: l2) ->
    filter f (l1 ++ x :: l2) = (l1' ++ x :: l2') ->
    filter f l1 = l1' /\ filter f l2 = l2'.
Proof.
  induction l1; intros; simpl in *; break_if; simpl in *; invc_NoDup.
  - destruct l1'; simpl in *.
    + solve_by_inversion.
    + find_inversion. exfalso. eauto using In_filter_In with *.
  - exfalso. eauto using In_filter_In with *.
  - destruct l1'; simpl in *; break_and; find_inversion.
    + exfalso. eauto with *.
    + find_apply_hyp_hyp. intuition auto using f_equal2.
  - eauto.
Qed.

Lemma map_inverses :
  forall A B (la : list A) (lb : list B)  (f : A -> B) g,
    (forall a, g (f a) = a) ->
    (forall b, f (g b) = b) ->
    lb = map f la ->
    la = map g lb.
Proof.
  destruct la; intros; simpl in *.
  - subst. reflexivity.
  - destruct lb; try congruence.
    simpl in *. find_inversion.
    find_higher_order_rewrite.
    f_equal.
    rewrite map_map.
    erewrite map_ext; [symmetry; apply map_id|].
    simpl in *. auto.
Qed.


Lemma In_notIn_implies_neq :
  forall A x y l,
    In(A:=A) x l ->
    ~ In(A:=A) y l ->
    x <> y.
Proof.
  intuition congruence.
Qed.

Lemma In_cons_neq :
  forall A a x xs,
    In(A:=A) a (x :: xs) ->
    a <> x ->
    In a xs.
Proof.
  simpl.
  intuition congruence.
Qed.

Lemma NoDup_app3_not_in_1 :
  forall A (xs ys zs : list A) b,
    NoDup (xs ++ ys ++ b :: zs) ->
    In b xs ->
    False.
Proof.
  intros.
  rewrite <- app_ass in *.
  find_apply_lem_hyp NoDup_remove.
  rewrite app_ass in *.
  intuition.
Qed.

Lemma NoDup_app3_not_in_2 :
  forall A (xs ys zs : list A) b,
    NoDup (xs ++ ys ++ b :: zs) ->
    In b ys ->
    False.
Proof.
  intros.
  rewrite <- app_ass in *.
  find_apply_lem_hyp NoDup_remove_2.
  rewrite app_ass in *.
  auto 10 with *.
Qed.

Lemma NoDup_app3_not_in_3 :
  forall A (xs ys zs : list A) b,
    NoDup (xs ++ ys ++ b :: zs) ->
    In b zs ->
    False.
Proof.
  intros.
  rewrite <- app_ass in *.
  find_apply_lem_hyp NoDup_remove_2.
  rewrite app_ass in *.
  auto 10 with *.
Qed.

Lemma In_cons_2_3 :
  forall A xs ys zs x y a,
    In (A:=A) a (xs ++ ys ++ zs) ->
    In a (xs ++ x :: ys ++ y :: zs).
Proof.
  intros.
  repeat (do_in_app; intuition auto 10 with *).
Qed.

Lemma In_cons_2_3_neq :
  forall A a x y xs ys zs,
    In (A:=A) a (xs ++ x :: ys ++ y :: zs) ->
    a <> x ->
    a <> y ->
    In a (xs ++ ys ++ zs).
Proof.
  intros.
  repeat (do_in_app; simpl in *; intuition (auto with *; try congruence)).
Qed.

Lemma in_middle_reduce :
  forall A a xs y zs,
    In (A:=A) a (xs ++ y :: zs) ->
    a <> y ->
    In a (xs ++ zs).
Proof.
  intros.
  do_in_app; simpl in *; intuition. congruence.
Qed.

Lemma in_middle_insert :
  forall A a xs y zs,
    In (A:=A) a (xs ++ zs) ->
    In a (xs ++ y :: zs).
Proof.
  intros.
  do_in_app; simpl in *; intuition.
Qed.

Lemma NoDup_rev :
  forall A l,
    NoDup (A:=A) l ->
    NoDup (rev l).
Proof.
  induction l; intros; simpl.
  - auto.
  - apply NoDup_append.
    invc_NoDup.
    constructor; auto.
    intuition.
    find_apply_lem_hyp in_rev.
    auto.
Qed.

Lemma NoDup_map_map :
  forall A B C (f : A -> B) (g : A -> C) xs,
    (forall x y, In x xs -> In y xs -> f x = f y -> g x = g y) ->
    NoDup (map g xs) ->
    NoDup (map f xs).
Proof.
  induction xs; intros; simpl in *.
  - constructor.
  - invc_NoDup.
    constructor; auto.
    intro.
    do_in_map.
    find_apply_hyp_hyp.
    find_reverse_rewrite.
    auto using in_map.
Qed.

Lemma plus_gt_0 :
  forall a b,
    a + b > 0 ->
    a > 0 \/ b > 0.
Proof.
  intros.
  destruct (eq_nat_dec a 0); intuition.
Qed.

Lemma pigeon :
  forall A (A_eq_dec : forall a a': A, {a = a'} + {a <> a'}) (l : list A) sub1 sub2,
    (forall a, In a sub1 -> In a l) ->
    (forall a, In a sub2 -> In a l) ->
    NoDup l ->
    NoDup sub1 ->
    NoDup sub2 ->
    length sub1 + length sub2 > length l ->
    exists a, In a sub1 /\ In a sub2.
Proof.
  induction l.
  intros.
  + simpl in *. find_apply_lem_hyp plus_gt_0. intuition.
    * destruct sub1; simpl in *; [omega|].
      specialize (H a). intuition.
    * destruct sub2; simpl in *; [omega|].
      specialize (H0 a). intuition.
  + intros. simpl in *.
    destruct (in_dec A_eq_dec a sub1);
      destruct (in_dec A_eq_dec a sub2); eauto;
      specialize (IHl (remove A_eq_dec a sub1) (remove A_eq_dec a sub2));
      cut (exists a0, In a0 (remove A_eq_dec a sub1) /\ In a0 (remove A_eq_dec a sub2));
      try solve [intros; break_exists;
                 intuition eauto using in_remove];
      apply IHl; try solve [
                       intros; find_copy_apply_lem_hyp in_remove;
                       find_apply_hyp_hyp; intuition; subst; exfalso; eapply remove_In; eauto];
      eauto using remove_NoDup; try solve_by_inversion;
      repeat match goal with
               | H : ~ In a ?sub |- _ =>
                 assert (length (remove A_eq_dec a sub) = length sub)
                   by eauto using remove_length_not_in; clear H
               | H : In a ?sub |- _ =>
                 assert (length (remove A_eq_dec a sub) >= length sub - 1)
                   by eauto using remove_length_ge; clear H
             end; omega.
Qed.

Lemma snoc_assoc :
  forall A (l : list A) x y,
    l ++ [x; y] = (l ++ [x]) ++ [y].
Proof.
  induction l; intros; simpl; intuition.
  auto using f_equal.
Qed.

Lemma cons_cons_app :
  forall A (x y : A),
    [x; y] = [x] ++ [y].
Proof.
  auto.
Qed.

Lemma map_partition :
  forall A B p l (x : B) p' (f : A -> B),
    map f l = (p ++ x :: p') ->
    exists ap a ap',
      l = ap ++ a :: ap' /\
      map f ap = p /\
      f a = x /\
      map f ap' = p'.
Proof.
  induction p; intros; intuition; simpl in *.
  - destruct l; simpl in *; try congruence.
    find_inversion.
    exists [],a,l. simpl. auto.
  - destruct l; simpl in *; try congruence.
    find_inversion.
    find_apply_hyp_hyp.
    break_exists_name ap.
    break_exists_name a.
    break_exists_name ap'.
    intuition.
    exists (a0 :: ap), a, ap'. simpl.
    repeat find_rewrite. intuition.
Qed.

Lemma map_eq_inv :
  forall (A B : Type) (f : A -> B) (l : list A) xs ys,
    map f l = xs ++ ys ->
    exists l1, exists l2, l = l1 ++ l2 /\ map f l1 = xs /\ map f l2 = ys.
Proof.
  induction l; simpl; intros xs ys H.
  - symmetry in H. apply app_eq_nil in H. break_and. subst.
    exists [], []. auto.
  - destruct xs; simpl in *.
    + exists [], (a :: l). intuition.
    + invc H. find_apply_hyp_hyp.
      break_exists_name l1.
      break_exists_name l2.
      break_and.
      exists (a :: l1), l2. subst.
      intuition.
Qed.

Lemma map_eq_inv_eq :
  forall (A B : Type) (f : A -> B),
    (forall a a', f a = f a' -> a = a') ->
    forall l l', map f l = map f l' -> l = l'.
Proof.
  induction l; simpl; intros l' Heq; destruct l'; simpl in *; try congruence.
  find_inversion. auto using f_equal2.
Qed.

Lemma map_fst_snd_id :
  forall A B l, map (fun t : A * B => (fst t, snd t)) l = l.
Proof.
  intros.
  rewrite <- map_id.
  apply map_ext.
  destruct a; auto.
Qed.
