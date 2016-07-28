Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListUtil.
Require Import StructTact.RemoveAll.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Sorting.Permutation.
Require Import Relation_Definitions.
Require Import RelationClasses.

Definition update2 {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (f : A -> A -> B) (x y : A) (v : B) :=
  fun x' y' => if sumbool_and _ _ _ _ (A_eq_dec x x') (A_eq_dec y y') then v else f x' y'.

Fixpoint collate {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (from : A) (f : A -> A -> list B) (ms : list (A * B)) :=
  match ms with
   | [] => f
   | (to, m) :: ms' => collate A_eq_dec from (update2 A_eq_dec f from to (f from to ++ [m])) ms'
  end.

Fixpoint collate_ls {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (s : list A) (f : A -> A -> list B) (to : A) (m : B) :=
  match s with
   | [] => f
   | from :: s' => collate_ls A_eq_dec s' (update2 A_eq_dec f from to (f from to ++ [m])) to m
  end.

Fixpoint filter_rel {A : Type} {rel : relation A} (A_rel_dec : forall x y : A, {rel x y} + {~ rel x y}) (x : A) (l : list A) :=
  match l with
   | [] => []
   | y :: tl => if A_rel_dec x y then y :: filter_rel A_rel_dec x tl else filter_rel A_rel_dec x tl
  end.

Definition map_fst {A B : Type} (a : A) := map (fun (b : B) => (a, b)).

Definition map_snd {A B : Type} (b : B) := map (fun (a : A) => (a, b)).

Require Import mathcomp.ssreflect.ssreflect.

Section update2.

Variable A B : Type.
Variable rel : relation A.

Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.
Hypothesis A_rel_dec : forall x y : A, {rel x y} + {~ rel x y}.
  
Lemma filter_rel_related :
  forall n n' ns,
  In n' (filter_rel A_rel_dec n ns) -> 
  In n' ns /\ rel n n'.
Proof.
move => n n' ns H_in.
elim: ns H_in => //=.
move => a l IH.
case A_rel_dec => H_dec H_in.
  case: H_in => H_in.
    rewrite H_in.
    rewrite H_in in H_dec.
    split => //.
    by left.
  concludes.
  break_and.
  split => //.
  by right.
concludes.
break_and.
split => //.
by right.
Qed.

Lemma related_filter_rel : 
  forall n n' ns,
    In n' ns -> 
    rel n n' ->
    In n' (filter_rel A_rel_dec n ns).
Proof.
move => n n' ns H_in H_adj.
elim: ns H_in => //=.
move => a l IH H_in.
case A_rel_dec => H_dec.
  case: H_in => H_in; first by left.
  concludes.
  by right.
case: H_in => H_in; first by subst; auto.
by concludes.
Qed.

Lemma not_in_not_in_filter_rel :
  forall ns n h,
    ~ In n ns ->
    ~ In n (filter_rel A_rel_dec h ns).
Proof.
elim => //=.
move => n' ns IH n h H_in.
have H_neq: n' <> n by move => H_neq; case: H_in; left.
have H_not_in: ~ In n ns by move => H_in'; case: H_in; right.
case A_rel_dec => H_dec; last exact: IH.
move => H_in'.
case: H_in' => H_in' //.
contradict H_in'.
exact: IH.
Qed.

Lemma NoDup_filter_rel:
  forall h ns,
    NoDup ns ->
    NoDup (filter_rel A_rel_dec h ns).
Proof.
move => h m.
elim => //=; first exact: NoDup_nil.
move => n ns H_in H_nd.
case A_rel_dec => H_dec //.
apply NoDup_cons.
exact: not_in_not_in_filter_rel.
Qed.

Lemma filter_rel_self_eq {irreflexive_rel : Irreflexive rel} :
  forall ns0 ns1 h,
  filter_rel A_rel_dec h (ns0 ++ h :: ns1) = filter_rel A_rel_dec h (ns0 ++ ns1).
Proof.
elim => [|n ns0 IH] ns1 h /=.
  case (A_rel_dec _ _) => /= H_dec //.
  by apply irreflexive_rel in H_dec.
case (A_rel_dec _ _) => /= H_dec //.
by rewrite IH.
Qed.

Lemma collate_f_eq :
  forall (f : A -> A -> list B) g h n n' l,
  f n n' = g n n' ->
  collate A_eq_dec h f l n n' = collate A_eq_dec h g l n n'.
Proof.
move => f g h n n' l.
elim: l f g => //.
case => n0 m l IH f g H_eq.
rewrite /=.
set f' := update2 _ _ _ _ _.
set g' := update2 _ _ _ _ _.
rewrite (IH f' g') //.
rewrite /f' /g' {f' g'}.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq_h H_eq_n].
rewrite -H_eq_h -H_eq_n in H_eq.
by rewrite H_eq.
Qed.

Lemma collate_in_in :
  forall l h n n' (f : A -> A -> list B) a,
    In a (f n' n) ->
    In a ((collate A_eq_dec h f l) n' n).
Proof.
elim => //=.
case => n0 mg' l IH h n n' f mg H_in.
apply IH.
rewrite /update2.
case sumbool_and => H_dec //.
move: H_dec => [H_eq H_eq'].
apply in_or_app.
left.
by rewrite H_eq H_eq'.
Qed.

Lemma collate_neq :
  forall h n n' ns (f : A -> A -> list B),
    h <> n ->
    collate A_eq_dec h f ns n n' = f n n'.
Proof.
move => h n n' ns f H_neq.
move: f.
elim: ns => //.
case.
move => n0 mg ms IH f.
rewrite /=.
rewrite IH.
rewrite /update2 /=.
case (sumbool_and _ _) => H_and //.
by move: H_and => [H_and H_and'].
Qed.

Lemma collate_not_in_eq :
  forall h' h (f : A -> A -> list B) l,
 ~ In h (map (fun nm : A * B => fst nm) l) -> 
  collate A_eq_dec h' f l h' h = f h' h.
Proof.
move => h' h f l.
elim: l f => //=.
case => n m l IH f H_in.
rewrite IH /update2.
  case (sumbool_and _ _ _ _) => H_dec //.
  by case: H_in; left; move: H_dec => [H_eq H_eq'].
move => H_in'.
case: H_in.
by right.
Qed.

Lemma collate_app :
  forall h' l1 l2 (f : A -> A -> list B),
  collate A_eq_dec h' f (l1 ++ l2) = collate A_eq_dec h' (collate A_eq_dec h' f l1) l2.
Proof.
move => h'.
elim => //.
case => n m l1 IH l2 f.
rewrite /=.
by rewrite IH.
Qed.

Lemma collate_neq_update2 :
  forall h h' n (f : A -> A -> list B) l ms,
  n <> h' ->
  collate A_eq_dec h (update2 A_eq_dec f h n ms) l h h' = collate A_eq_dec h f l h h'.
Proof.
move => h h' n f l ms H_neq.
have H_eq: update2 A_eq_dec f h n ms h h' =  f h h'.
  rewrite /update2 /=.
  by case (sumbool_and _ _ _ _) => H_eq; first by move: H_eq => [H_eq H_eq'].
by rewrite (collate_f_eq _ _ _ _ _ _ H_eq).
Qed.

Lemma collate_not_in :
  forall h h' l1 l2 (f : A -> A -> list B),
  ~ In h' (map (fun nm : A * B => fst nm) l1) ->
  collate A_eq_dec h f (l1 ++ l2) h h' = collate A_eq_dec h f l2 h h'.
Proof.
move => h h' l1 l2 f H_in.
rewrite collate_app.
elim: l1 f H_in => //.
case => n m l IH f H_in.
rewrite /= IH.
  have H_neq: n <> h' by move => H_eq; case: H_in; left.
  by rewrite collate_neq_update2.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma collate_not_in_mid :
 forall h h' l1 l2 (f : A -> A -> list B) m,
   ~ In h (map (fun nm : A * B => fst nm) (l1 ++ l2)) ->
   collate A_eq_dec h' (update2 A_eq_dec f h' h (f h' h ++ [m])) (l1 ++ l2) = collate A_eq_dec h' f (l1 ++ (h, m) :: l2).
Proof.
move => h h' l1 l2 f m H_in.
apply functional_extensionality => from.
apply functional_extensionality => to.
case (A_eq_dec h' from) => H_dec.
  rewrite -H_dec.
  case (A_eq_dec h to) => H_dec'.
    rewrite -H_dec'.
    rewrite collate_not_in; last first.
      move => H_in'.
      case: H_in.
      rewrite map_app.
      apply in_or_app.
      by left.
    rewrite collate_not_in //.
    move => H_in'.
    case: H_in.
    rewrite map_app.
    apply in_or_app.
    by left.
  rewrite collate_neq_update2 //.
  rewrite 2!collate_app.
  rewrite /=.
  by rewrite collate_neq_update2.
rewrite collate_neq //.
rewrite collate_neq //.
rewrite /update2 /=.
case (sumbool_and _ _) => H_dec' //.
by move: H_dec' => [H_eq H_eq'].
Qed.

Lemma NoDup_perm_collate_eq :
  forall h (f : A -> A -> list B) l l',
    NoDup (map (fun nm => fst nm) l) ->
    Permutation l l' ->
    collate A_eq_dec h f l = collate A_eq_dec h f l'.
Proof.
move => h f l.
elim: l h f.
  move => h f l' H_nd H_pm.
  apply Permutation_nil in H_pm.
  by rewrite H_pm.
case => h m l IH h' f l' H_nd.
rewrite /= in H_nd.
inversion H_nd; subst.
move => H_pm.
rewrite /=.
have H_in': In (h, m) ((h, m) :: l) by left.
have H_pm' := Permutation_in _ H_pm H_in'.
apply in_split in H_pm'.
move: H_pm' => [l1 [l2 H_eq]].
rewrite H_eq.
rewrite H_eq in H_pm.
apply Permutation_cons_app_inv in H_pm.
have IH' := IH h' (update2 A_eq_dec f h' h (f h' h ++ [m])) _ H2 H_pm.
rewrite IH'.
rewrite collate_not_in_mid //.
move => H_in.
case: H1.
suff H_pm': Permutation (map (fun nm : A * B => fst nm) l) (map (fun nm : A * B => fst nm) (l1 ++ l2)).
  move: H_in.
  apply Permutation_in.
  exact: Permutation_sym.
exact: Permutation_map_fst.
Qed.

Lemma collate_map_pair_not_related :
  forall m n h ns (f : A -> A -> list B),
    ~ rel h n ->
    collate A_eq_dec h f (map_snd m (filter_rel A_rel_dec h ns)) h n = f h n.
Proof.
move => m n h ns f H_adj.
move: f.
elim: ns => //.
move => n' ns IH f.
rewrite /=.
case (A_rel_dec _ _) => H_dec' //.
rewrite /=.
rewrite IH.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_adj.
Qed.

Lemma collate_map_snd_notin :
  forall m' n h ns (f : A -> A -> list B),
    ~ In n ns ->
    collate A_eq_dec h f (map_snd m' (filter_rel A_rel_dec h ns)) h n = f h n.
Proof.
move => m' n h ns f.
move: f.
elim: ns => //.
move => n' ns IH f H_in.
rewrite /=.
case (A_rel_dec _ _) => H_dec'.
  rewrite /=.
  rewrite IH.
    rewrite /update2.
    case (sumbool_and _ _) => H_and //.
    move: H_and => [H_and H_and'].
    rewrite H_and' in H_in.
    by case: H_in; left.
  move => H_in'.
  case: H_in.
  by right.
rewrite IH //.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma collate_map_snd_notin_remove_all :
  forall m n h ns (f : A -> A -> list B) failed,
    ~ In n ns ->
    collate A_eq_dec h f (map_snd m (filter_rel A_rel_dec h (remove_all A_eq_dec failed ns))) h n = f h n.
Proof.
move => m n h ns f failed H_in.
apply collate_map_snd_notin.
move => H_ex.
by find_apply_lem_hyp in_remove_all_was_in.
Qed.

Lemma collate_map_snd_live_related :
  forall m n h ns (f : A -> A -> list B) failed,
    ~ In n failed ->
    rel h n ->
    In n ns ->
    NoDup ns ->
    collate A_eq_dec h f (map_snd m (filter_rel A_rel_dec h (remove_all A_eq_dec failed ns))) h n = f h n ++ [m].
Proof.
move => m n h ns f failed H_in H_adj.
move: f.
elim: ns => //.
move => n' ns IH f H_in' H_nd.
inversion H_nd; subst.
case: H_in' => H_in'.
  rewrite H_in'.
  subst.
  have H_ra := remove_all_cons A_eq_dec failed n ns.
  break_or_hyp; break_and => //.
  find_rewrite.
  rewrite /=.
  case (A_rel_dec _ _) => H_dec' //=.
  rewrite collate_map_snd_notin_remove_all //.
  rewrite /update2.
  case (sumbool_and _ _) => H_sumb //.
  by case: H_sumb.    
have H_neq: n' <> n by move => H_eq; rewrite -H_eq in H_in'. 
have H_ra := remove_all_cons A_eq_dec failed n' ns.
break_or_hyp; break_and; first by find_rewrite; rewrite IH.
find_rewrite.
rewrite /=.
case A_rel_dec => /= H_dec'; rewrite IH //.
rewrite /update2.
case (sumbool_and _ _) => H_sumb //.
by move: H_sumb => [H_eq H_eq'].
Qed.

Lemma collate_map_snd_in_failed :
  forall m' n h ns (f : A -> A -> list B) failed,
    In n failed ->
    collate A_eq_dec h f (map_snd m' (filter_rel A_rel_dec h (remove_all A_eq_dec failed ns))) h n = f h n.
Proof.
move => m' n h ns f failed.
move: f.
elim: ns => /=; first by rewrite remove_all_nil.
move => n' ns IH f H_in.
have H_ra := remove_all_cons A_eq_dec failed n' ns.
break_or_hyp; break_and; find_rewrite; first by rewrite IH.
rewrite /=.
case A_rel_dec => H_dec'; last by rewrite IH.
rewrite /= IH //.
rewrite /update2.
case (sumbool_and _ _) => H_and //.
move: H_and => [H_and H_and'].
by rewrite -H_and' in H_in.
Qed.

Lemma collate_map_pair_live_related_alt :
  forall a n h ns (f : A -> A -> list B),
    rel h n ->
    ~ In n ns ->
    collate A_eq_dec h f (map_snd a (filter_rel A_rel_dec h (n :: ns))) h n = f h n ++ [a].
Proof.
move => a n h ns f H_adj H_in /=.
case A_rel_dec => /= H_dec // {H_dec}.
move: f n h H_in H_adj.
elim: ns  => //=.
  move => f n h H_in.
  rewrite /update2.
  case (sumbool_and _ _ _ _) => H_and //.
  by case: H_and => H_and.
move => n' ns IH f n h H_in H_adj.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
have H_neq: n <> n' by move => H_eq; case: H_in; left.
case A_rel_dec => /= H_dec; last by rewrite IH.
rewrite {3}/update2.
case sumbool_and => H_and; first by move: H_and => [H_and H_and'].
have IH' := IH f.
rewrite collate_map_snd_notin //.
rewrite /update2.
case sumbool_and => H_and'; first by move: H_and' => [H_and' H_and'']; rewrite H_and'' in H_neq.
case sumbool_and => H_and'' //.
by case: H_and''.
Qed.

Lemma in_collate_in :
  forall ns n h (f : A -> A -> list B) a,
  ~ In n ns ->
  In a ((collate A_eq_dec h f (map_snd a (filter_rel A_rel_dec h ns))) h n) ->
  In a (f h n).
Proof.
elim => //=.
move => n' ns IH n h f mg H_in.
have H_neq: n' <> n by move => H_eq; case: H_in; left.
have H_in': ~ In n ns by move => H_in'; case: H_in; right.
case A_rel_dec => H_dec; last exact: IH.
rewrite /=.
set up2 := update2 _ _ _ _ _.
have H_eq_f: up2 h n = f h n.
  rewrite /up2 /update2.
  by case sumbool_and => H_and; first by move: H_and => [H_eq H_eq'].
rewrite (collate_f_eq _ _ _ _ _ _ H_eq_f).
exact: IH.
Qed.

Lemma not_in_map_pair :
  forall n h (m : B) ns,
    ~ In n ns ->
    ~ In (n, m) (map_snd m (filter_rel A_rel_dec h ns)).
Proof.
move => n h m.
elim => //=.
move => n' ns IH H_in.
case (A_rel_dec _ _) => H_dec.
  rewrite /=.
  move => H_in'.
  case: H_in' => H_in'.
    inversion H_in'.
    by case: H_in; left.
  contradict H_in'.
  apply: IH.
  move => H_in'.
  case: H_in.
  by right.
apply: IH.
move => H_in'.
case: H_in.
by right.
Qed.

Lemma NoDup_map_snd :
  forall h (m : B) ns,
    NoDup ns ->
    NoDup (map_snd m (filter_rel A_rel_dec h ns)).
Proof.
move => h m.
elim => //=.
  move => H_nd.
  exact: NoDup_nil.
move => n ns IH H_in.
inversion H_in.
case (A_rel_dec _ _) => H_dec.
  rewrite /=.
  apply NoDup_cons.
    apply IH in H2.
    exact: not_in_map_pair.
  exact: IH.
exact: IH.
Qed.

Lemma in_for_msg :
  forall h (m : B) ns nm,
  In nm (map_snd m (filter_rel A_rel_dec h ns)) ->
  snd nm = m.
Proof.
move => h m.
elim => //.
move => n l IH.
case => /= n' m'.
case (A_rel_dec _ _) => H_dec.
  rewrite /=.
  move => H_in.
  case: H_in => H_in; first by inversion H_in.
  have ->: m' = snd (n', m') by [].
  exact: IH.
move => H_in.
have ->: m' = snd (n', m') by [].
exact: IH.
Qed.

Lemma in_map_snd_related_in :
  forall (m : B) ns n h,
  In (n, m) (map_snd m (filter_rel A_rel_dec h ns)) ->
  rel h n /\ In n ns.
Proof.
move => m.
elim => //=.
move => n ns IH n' h.
case (A_rel_dec _ _) => /= H_dec.
  move => H_in.
  case: H_in => H_in.
    inversion H_in.
    rewrite H0 in H_dec.
    split => //.
    by left.
  apply IH in H_in.
  move: H_in => [H_adj H_in].
  split => //.
  by right.
move => H_in.
apply IH in H_in.
move: H_in => [H_adj H_in].
split => //.
by right.
Qed.

Lemma collate_ls_not_in :
  forall ns (f : A -> A -> list B) h mg from to,
    ~ In from ns ->
    collate_ls A_eq_dec ns f h mg from to = f from to.
Proof.
elim => //=.
move => n ns IH f h mg from to H_in.
have H_neq: n <> from by move => H_eq; case: H_in; left.
have H_in': ~ In from ns by move => H_in'; case: H_in; right.
rewrite IH //.
rewrite /update2.
case sumbool_and => H_dec //.
by move: H_dec => [H_eq H_eq'].
Qed.

Lemma collate_ls_neq_to : 
  forall ns (f : A -> A -> list B) h mg from to,
    h <> to ->
    collate_ls A_eq_dec ns f h mg from to = f from to.
Proof.
elim => //=.
move => n ns IH f h mg from to H_neq.
rewrite IH //.
rewrite /update2.
case sumbool_and => H_dec //.
by move: H_dec => [H_eq H_eq'].
Qed.

Lemma collate_ls_NoDup_in :
  forall ns (f : A -> A -> list B) h mg from,
  NoDup ns ->
  In from ns ->
  collate_ls A_eq_dec ns f h mg from h = f from h ++ [mg].
Proof.
elim => //=.
move => n ns IH f h mg from H_nd H_in.
inversion H_nd; subst.
break_or_hyp.
  rewrite collate_ls_not_in //.
  rewrite /update2.
  by case sumbool_and => H_dec; last break_or_hyp.    
have H_neq: n <> from by move => H_eq; find_rewrite.
rewrite IH //.
rewrite /update2.
by case sumbool_and => H_dec; first by break_and; find_rewrite.
Qed.

Lemma collate_ls_live_related : 
  forall ns (f : A -> A -> list B) failed h mg from,
  ~ In from failed ->
  rel h from ->
  In from ns ->
  NoDup ns ->     
  collate_ls A_eq_dec (filter_rel A_rel_dec h (remove_all A_eq_dec failed ns)) f h mg from h = f from h ++ [mg].
Proof.
move => ns f failed h mg from.
move => H_f H_adj H_in H_nd.
rewrite collate_ls_NoDup_in //; first by apply: NoDup_filter_rel; exact: NoDup_remove_all.
apply related_filter_rel => //.
exact: in_remove_all_preserve.
Qed.

Lemma collate_ls_f_eq :
  forall ns (f : A -> A -> list B) g h mg n n',
  f n n' = g n n' ->
  collate_ls A_eq_dec ns f h mg n n' = collate_ls A_eq_dec ns g h mg n n'.
Proof.
elim => //=.
move => n0 ns IH f g h mg n n' H_eq.
set f' := update2 _ _ _ _ _.
set g' := update2 _ _ _ _ _.
rewrite (IH f' g') //.
rewrite /f' /g' {f' g'}.
rewrite /update2 /=.
case sumbool_and => H_dec //.
by break_and; repeat find_rewrite.
Qed.

Lemma collate_ls_neq_update2 : 
  forall ns (f : A -> A -> list B) n h h' ms mg,
  n <> h' ->
  collate_ls A_eq_dec ns (update2 A_eq_dec f n h ms) h mg h' h = collate_ls A_eq_dec ns f h mg h' h.
Proof.
move => ns f n h h' ms mg H_neq.
have H_eq: update2 A_eq_dec f n h ms h' h = f h' h.
  rewrite /update2.
  by case sumbool_and => H_eq; first by break_and; find_rewrite.
by rewrite (collate_ls_f_eq _ _ _ _ _ _ _ H_eq).
Qed.

Lemma collate_ls_not_related :
  forall ns (f : A -> A -> list B) n h mg,
    ~ rel h n ->
    collate_ls A_eq_dec (filter_rel A_rel_dec h ns) f h mg n h = f n h.
Proof.
elim => //=.
move => n' ns IH f n h mg H_adj.
case (A_eq_dec n n') => H_dec.
  rewrite -H_dec.
  case A_rel_dec => H_dec' //=.
  by rewrite IH.
case A_rel_dec => H_dec' /=; last by rewrite IH.
rewrite IH //.
rewrite /update2.
by case sumbool_and => H_and; first by break_and; find_rewrite.
Qed.

Lemma collate_ls_not_in_related :
  forall ns (f : A -> A -> list B) n h mg,
    ~ In n ns ->
    collate_ls A_eq_dec (filter_rel A_rel_dec h ns) f h mg n h = f n h.
Proof.
move => ns f n h mg H_in.
rewrite collate_ls_not_in //.
exact: not_in_not_in_filter_rel.
Qed.

Lemma collate_ls_not_in_related_exclude :
  forall ns (f : A -> A -> list B) n h mg failed,
    ~ In n ns ->
    collate_ls A_eq_dec (filter_rel A_rel_dec h (remove_all A_eq_dec failed ns)) f h mg n h = f n h.
Proof.
move => ns f n h mg failed H_in.
rewrite collate_ls_not_in //.
apply: not_in_not_in_filter_rel.
move => H_in'.
case: H_in.
move: H_in'.
exact: in_remove_all_was_in.
Qed.

Lemma collate_ls_in_excluded :
  forall mg n h ns (f : A -> A -> list B) failed,
    In n failed ->
    collate_ls A_eq_dec (filter_rel A_rel_dec h (remove_all A_eq_dec failed ns)) f h mg n h = f n h.
Proof.
move => mg n h ns f failed H_in.
move: f.
elim: ns; first by rewrite remove_all_nil.
move => n' ns IH f.
have H_cn := remove_all_cons A_eq_dec failed n' ns.
break_or_hyp; break_and; find_rewrite; first by rewrite IH.
rewrite /=.
case A_rel_dec => H_dec //=.
have H_neq: n' <> n by move => H_eq; rewrite -H_eq in H_in.
rewrite IH.
rewrite /update2.
by break_if; first by break_and.
Qed.

Lemma collate_ls_app :
  forall l1 l2 (f : A -> A -> list B) h m,
  collate_ls A_eq_dec (l1 ++ l2) f h m = collate_ls A_eq_dec l2 (collate_ls A_eq_dec l1 f h m) h m.
Proof. by elim => //=. Qed.

Lemma collate_ls_split_eq :
  forall l1 l2 (f : A -> A -> list B) h m from to,
  h <> from -> 
  collate_ls A_eq_dec (l1 ++ h :: l2) f to m from to =
  collate_ls A_eq_dec  (l1 ++ l2) f to m from to.
Proof.
elim => //=.
  move => l2 f h m from to H_neq.
  apply: collate_ls_f_eq.
  rewrite /update2.
  by break_if; first by break_and.
move => h' l1 IH l2 f h m from to H_neq.
by rewrite IH.
Qed.

Lemma collate_ls_not_in_mid :
 forall h h' l1 l2 (f : A -> A -> list B) m,
   ~ In h' (l1 ++ l2) ->
   collate_ls A_eq_dec (l1 ++ l2) (update2 A_eq_dec f h' h (f h' h ++ [m])) h m = collate_ls A_eq_dec (l1 ++ h' :: l2) f h m.
Proof.
move => h h' l1 l2 f m H_in.
apply functional_extensionality => from.
apply functional_extensionality => to.
case (A_eq_dec h' from) => H_dec; case (A_eq_dec h to) => H_dec'.
- rewrite -H_dec -H_dec'.
  rewrite collate_ls_not_in //.
  rewrite collate_ls_app /=.
  set f' := collate_ls _ l1 _ _ _.
  rewrite collate_ls_not_in; last first.
    move => H_in'.
    case: H_in.
    apply in_or_app.
    by right.
  rewrite {2}/update2.
  break_if; last by break_or_hyp.
  rewrite /f'.
  rewrite collate_ls_not_in; last first.
    move => H_in'.
    case: H_in.
    apply in_or_app.
    by left.
  rewrite /update2.
  by break_if; last by break_or_hyp.
- rewrite collate_ls_neq_to //.
  rewrite collate_ls_neq_to //.
  rewrite /update2.
  by break_if; first by break_and.
- rewrite H_dec' collate_ls_neq_update2 //.
  by rewrite collate_ls_split_eq.
- rewrite collate_ls_neq_to //.
  rewrite collate_ls_neq_to //.
  rewrite /update2.
  by break_if; first by break_and.
Qed.

Lemma NoDup_perm_collate_ls_eq :
  forall l (f : A -> A -> list B) h m l',
    NoDup l ->
    Permutation l l' ->
    collate_ls A_eq_dec l f h m = collate_ls A_eq_dec l' f h m.
Proof.
move => l f h m l'.
elim: l f l'.
  move => f l' H_nd H_pm.
  apply Permutation_nil in H_pm.
  by rewrite H_pm.
move => a l IH f l' H_nd H_pm.
inversion H_nd; subst_max.
rewrite /=.
have H_in: In a (a :: l) by left.
have H_pm' := Permutation_in _ H_pm H_in.
find_apply_lem_hyp in_split.
break_exists.
subst_max.
apply Permutation_cons_app_inv in H_pm.
set f' := update2 _ _ _ _ _.
rewrite (IH f' _ _ H_pm) //.
rewrite collate_ls_not_in_mid //.
move => H_in'.
case: H1.
move: H_in'.
apply Permutation_in.
exact: Permutation_sym.
Qed.

End update2.
