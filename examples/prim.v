Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Export Coq.Classes.EquivDec.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted path path_basic vpath epath Zweight.
From GraphLib.undirected Require Import tree.
From MaxMinLib Require Import MaxMin Interface. 
From ListLib Require Import General.NoDup.


Local Open Scope sets.
Local Open Scope Z.

Section prim.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noempty: NoEmptyEdge G V E}
        {undirected: UndirectedGraph G V E}
        {stepuniq: StepUniqueUndirected G V E}
        (g: G)
        {eq_dec_E: EqDec E eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Context (g_valid: gvalid g).

Definition acyclic_eset (elist: list E): Prop := 
  ~ exists u p, 
    p <> nil /\ 
    is_simple_epath g u p u /\ 
    Forall (fun x => In x elist) p.

Definition spans_all_vertices (elist: list E): Prop :=
  forall u v,
    vvalid g u -> vvalid g v ->
    exists p, valid_epath g u p v /\ Forall (fun x => In x elist) p.


Definition is_spanning_tree (elist: list E): Prop :=
  (forall e, In e elist -> evalid g e) /\
  spans_all_vertices elist /\
  acyclic_eset elist.

Definition total_weight (elist: list E): option Z :=
  fold_right (fun e l => Z_op_plus (weight g e) l) (Some 0) elist.

Definition is_mst (elist: list E): Prop :=
  min_object_of_subset
    Z_op_le (fun elist => NoDup elist /\ is_spanning_tree elist) total_weight elist.

Fixpoint remove_once (e: E) (elist: list E) : list E :=
  match elist with
  | nil => nil
  | e' :: elist' =>
      if eq_dec_E e e'
      then elist'
      else e' :: remove_once e elist'
  end.

Definition swap_cons (e e' : E) (elist : list E) : list E :=
  e :: remove_once e' elist.

(** 用新边 [e] 替换旧边 [e']（[swap_cons]）后，原边 [e'] 被移除，
    原边 [e'] 的可达性由新边 [e] 保持。 *)
Definition swap_reconnects_removed_edge_fixed
  (e e' : E) (elist : list E) : Prop :=
  forall u' v',
    step_aux g e' u' v' ->  
    exists p, valid_epath g u' p v' /\ Forall (fun x => In x (swap_cons e e' elist)) p.

(** 用新边 [e] 替换旧边 [e']（[swap_cons]）后，新边 [e] 不会形成环。 *)
Definition swap_keeps_new_edge_cycle_free_fixed
  (e e' : E) (elist : list E) : Prop :=
  forall u v,
    step_aux g e u v ->
    ~ exists p, valid_epath g u p v /\ Forall (fun x => In x (remove_once e' elist)) p.

(* ？ *)
Definition chosen_path_disconnects_after_removal
  (e e' : E) (elist : list E) : Prop :=
  forall u v p1 p2 y1 y2,
    step_aux g e u v ->
    valid_epath g u p1 y1 ->
    step_aux g e' y1 y2 ->
    valid_epath g y2 p2 v ->
    NoDup (p1 ++ e' :: p2) ->
    Forall (fun e => In e elist) (p1 ++ e' :: p2) ->
    ~ exists p, valid_epath g u p v /\ Forall (fun e => In e (remove_once e' elist)) p.

Lemma acyclic_eset_empty :
  acyclic_eset nil.
Proof.
  unfold acyclic_eset.
  intros [u [p [Hp_nonempty [_ Hp_forall]]]].
  destruct p as [|e p'].
  - contradiction.
  - inversion Hp_forall.
    contradiction.
Qed.

Lemma remove_once_in_elim :
  forall e e' elist,
    In e (remove_once e' elist) ->
    In e elist.
Proof.
  intros e e' elist.
  induction elist as [|x xs IH]; simpl; try tauto.
  destruct (eq_dec_E e' x); simpl; auto.
  intros [Heq | Hin]; [left|right]; auto.
Qed.

Lemma remove_once_not_in :
  forall e elist,
    NoDup elist ->
    ~ In e (remove_once e elist).
Proof.
  intros e elist Hnd.
  induction Hnd as [|e' elist Hnotin Hnd IH]; simpl.
  - tauto.
  - destruct (eq_dec_E e e') as [Heq_dec | Hneq].
    + destruct Heq_dec. exact Hnotin.
    + simpl. intros [Heq | Hin].
      * apply Hneq. symmetry; exact Heq.
      * auto.
Qed.

Lemma valid_epath_simple_preserve_Forall :
  forall eset u p v,
    valid_epath g u p v ->
    Forall eset p ->
    exists q, is_simple_epath g u q v /\ Forall eset q.
Proof.
  intros eset u p v H_valid Hfor.
  remember (length p) as n.
  revert u p v H_valid Hfor Heqn.
  induction n using lt_wf_ind; intros u p v H_valid Hfor Heqn.
  destruct (classic (NoDup p)).
  - exists p. split; [split|]; auto.
  - apply Nodup_exists_repetition in H0.
    destruct H0 as [e [l1 [l2 [l3 H_eq]]]].
    subst p.
    assert ((forall (e : E) (x1 y1 x2 y2 : V),
      step_aux g e x1 y1 ->
      step_aux g e x2 y2 ->
      x1 = x2 /\ y1 = y2 \/ x1 = y2 /\ x2 = y1)). { 
        intros. eapply step_aux_unique_undirected in H0. 3:{apply H1. } 
        destruct H0 as [[]|[]]; subst; auto. auto. 
    }
    pose proof (@valid_epath_shorten_cycle _ _ _ pg _ P _ _ _ _ _ g H0 u v l1 e l2 l3 H_valid) 
    as [q [Hqpath [Hqlt Hsub]]].
    apply (H (length q)) in Hqpath; auto.
    lia.
    rewrite Forall_forall in *. 
    intros x Hin; auto. 
Qed.

Lemma Forall_edge_set_neq_of_notin :
  forall (elist: list E) e p,
    Forall (fun e => In e elist) p ->
    ~ In e p ->
    Forall (fun x => In x elist /\ x <> e) p.
Proof.
  intros elist e p Hfor Hnotin.
  rewrite Forall_forall in *.
  intros x Hin.
  split.
  - apply Hfor; exact Hin.
  - intro Heq.
    apply Hnotin.
    subst x.
    exact Hin.
Qed.

Lemma Forall_remove_once_old_neq :
  forall elist e p,
    NoDup elist ->
    Forall (fun x => In x (remove_once e elist)) p ->
    Forall (fun x => In x elist /\ x <> e) p.
Proof.
  intros elist e p Hnd Hfor.
  rewrite Forall_forall in *.
  intros x Hin.
  pose proof (Hfor x Hin) as Hremove.
  split.
  - eapply remove_once_in_elim; eauto.
  - intro Heq.
    subst x.
    pose proof (remove_once_not_in e elist Hnd) as Hnotin.
    contradiction.
Qed.

Lemma reachable_in_eset_valid_epath :
  forall eset u v,
    reachable_in_eset g eset u v ->
    exists p, valid_epath g u p v /\ Forall eset p.
Proof.
  intros eset u v Hreach.
  unfold reachable_in_eset in Hreach. 
  induction_1n Hreach.
  - exists nil.
    split.
    + apply valid_epath_empty.
    + constructor.
  - destruct H as [e [Hvalid Hfor]]. 
    apply IHrt in g_valid as [p [Hvalid' Hfor']]; auto.
    exists (e :: p).
    split.
    + eapply valid_epath_cons; eauto. 
    + constructor; auto.
Qed.

Lemma remove_once_in_preserved :
  forall e e' elist,
    e <> e' ->
    In e elist ->
    In e (remove_once e' elist).
Proof.
  intros e e' elist Hneq Hin.
  induction elist as [|x xs IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst x.
      destruct (eq_dec_E e' e) as [Heq_dec | Hneq'].
      * exfalso. apply Hneq. symmetry; exact Heq_dec.
      * simpl; auto.
    + destruct (eq_dec_E e' x) as [Heq_dec | Hneq'].
      * exact Hin.
      * simpl; right; auto.
Qed.

Lemma remove_once_NoDup :
  forall e elist,
    NoDup elist ->
    NoDup (remove_once e elist).
Proof.
  intros e elist Hnd.
  induction Hnd as [|x elist Hnotin Hnd IH]; simpl.
  - constructor.
  - destruct (eq_dec_E e x).
    + exact Hnd.
    + constructor.
      * intro Hin.
        apply Hnotin.
        eapply remove_once_in_elim; eauto.
      * exact IH.
Qed.

Lemma total_weight_remove_once :
  forall e elist,
    NoDup elist ->
    In e elist ->
    total_weight elist = Z_op_plus (weight g e) (total_weight (remove_once e elist)).
Proof.
  intros e elist Hnd Hin.
  induction Hnd as [|x xs Hnotin Hnd IH]; simpl in *; try contradiction.
  destruct Hin as [Heq | Hin].
  + subst x.
    destruct (eq_dec_E e e) as [_ | Hneq]; [reflexivity | exfalso; apply Hneq; reflexivity].
  + destruct (eq_dec_E e x) as [Heq_dec | Hneq].
    * exfalso.
      apply Hnotin.
      rewrite <- Heq_dec.
      exact Hin.
    * simpl.
      rewrite IH by exact Hin.
      rewrite Z_op_plus_assoc.
      rewrite (Z_op_plus_comm (weight g x) (weight g e)).
      rewrite <- Z_op_plus_assoc.
      reflexivity.
Qed.

Lemma total_weight_replace_le :
  forall e e' elist,
    NoDup elist ->
    In e' elist ->
    Z_op_le (weight g e) (weight g e') ->
    Z_op_le (total_weight (swap_cons e e' elist)) (total_weight elist).
Proof.
  intros e e' elist Hnd Hin Hle.
  simpl.
  rewrite (total_weight_remove_once e' elist Hnd Hin).
  apply Z_op_plus_mono; [assumption | apply Z_op_le_refl].
Qed.

Lemma swap_cons_NoDup :
  forall e e' elist,
    NoDup elist ->
    ~ In e (remove_once e' elist) ->
    NoDup (swap_cons e e' elist).
Proof.
  intros e e' elist Hnd Hnotin.
  unfold swap_cons.
  constructor.
  - exact Hnotin.
  - apply remove_once_NoDup.
    exact Hnd.
Qed.

Lemma swap_cons_contains_new :
  forall e e' elist,
    In e (swap_cons e e' elist).
Proof.
  intros e e' elist.
  unfold swap_cons.
  simpl; auto.
Qed.

Lemma swap_cons_contains_old :
  forall e e' elist x,
    x <> e' ->
    In x elist ->
    In x (swap_cons e e' elist).
Proof.
  intros e e' elist x Hneq Hin.
  unfold swap_cons in *.
  simpl.
  right.
  eapply remove_once_in_preserved; eauto.
Qed.

Lemma swap_cons_evalid :
  forall e e' elist,
    evalid g e ->
    (forall x, In x elist -> evalid g x) ->
    forall x, In x (swap_cons e e' elist) -> evalid g x.
Proof.
  intros e e' elist Hevalid Holdvalid x Hin.
  unfold swap_cons in Hin.
  simpl in Hin.
  destruct Hin as [Heq | Hin].
  - subst x. exact Hevalid.
  - apply Holdvalid.
    eapply remove_once_in_elim; eauto.
Qed.

Lemma remove_once_not_in_of_not_in :
  forall e e' elist,
    ~ In e elist ->
    ~ In e (remove_once e' elist).
Proof.
  intros e e' elist Hnotin Hin.
  apply Hnotin.
  eapply remove_once_in_elim; eauto.
Qed.

Lemma swap_cons_NoDup_if_fresh :
  forall e e' elist,
    NoDup elist ->
    ~ In e elist ->
    NoDup (swap_cons e e' elist).
Proof.
  intros e e' elist Hnd Hfresh.
  apply swap_cons_NoDup.
  - exact Hnd.
  - apply remove_once_not_in_of_not_in.
    exact Hfresh.
Qed.

Lemma swap_cons_valid_edges_if_spanning_tree :
  forall e e' elist,
    evalid g e ->
    is_spanning_tree elist ->
    forall x, In x (swap_cons e e' elist) -> evalid g x.
Proof.
  intros e e' elist Hevalid [Helist_valid _] x Hin.
  eapply swap_cons_evalid; eauto.
Qed.

Lemma edge_in_swap_not_new_removed :
  forall e e' elist x,
    In x (swap_cons e e' elist) ->
    x <> e ->
    In x (remove_once e' elist).
Proof.
  intros e e' elist x Hin Hneq.
  unfold swap_cons in *.
  simpl in Hin.
  destruct Hin as [Heq | Hin].
  - subst x. exfalso. apply Hneq. reflexivity.
  - exact Hin.
Qed.

Lemma Forall_swap_removed_if_not_new :
  forall e e' elist p,
    Forall (fun x => In x (swap_cons e e' elist)) p ->
    ~ In e p ->
    Forall (fun x => In x (remove_once e' elist)) p.
Proof.
  intros e e' elist p Hfor Hnotin.
  rewrite Forall_forall in *.
  intros x Hin.
  apply (edge_in_swap_not_new_removed e e' elist x).
  - eapply Hfor; eauto.
  - intro Heq.
    apply Hnotin.
    subst x; exact Hin.
Qed.

Lemma valid_epath_Forall_reachable_in_eset :
  forall eset u p v,
    valid_epath g u p v ->
    Forall eset p ->
    (exists p, valid_epath g u p v /\ Forall eset p).
Proof.
  intros eset u p v Hpath.
  revert u v Hpath.
  induction p as [|e p IH]; intros u v Hpath Hfor.
  - apply valid_epath_nil_inv in Hpath.
    subst v.
    exists nil.
    split; [exact (valid_epath_empty g u) | constructor].
  - inversion Hfor; subst.
    apply valid_epath_cons_inv in Hpath.
    destruct Hpath as [v0 [Hstep Hrest]].
    destruct (IH v0 v Hrest H2) as [p' [Hp'path Hp'for]].
    exists (e :: p').
    split; [eapply valid_epath_cons; eauto | constructor; auto].
Qed.

Lemma valid_epath_transfer_to_swap_fixed :
  forall e e' elist u p v,
    swap_reconnects_removed_edge_fixed e e' elist ->
    valid_epath g u p v ->
    Forall (fun x => In x elist) p ->
    exists p, valid_epath g u p v /\ Forall (fun x => In x (swap_cons e e' elist)) p.
Proof.
  intros e e' elist u p v Hreconn Hpath.
  revert u v Hpath.
  induction p as [|a p IH]; intros u v Hpath Hfor.
  - apply valid_epath_nil_inv in Hpath.
    subst v.
    exists nil.
    split; [exact (valid_epath_empty g u) | constructor].
  - inversion Hfor; subst.
    apply valid_epath_cons_inv in Hpath.
    destruct Hpath as [v0 [Hstep Hrest]].
    destruct (eq_dec_E a e') as [Heq | Hneq].
    + destruct Heq. 
      pose proof Hreconn u v0 Hstep as [q [Hqpath Hqfor]].
      destruct (IH v0 v Hrest H2) as [p' [Hp'path Hp'for]].
      exists (q ++ p').
      split; [eapply valid_epath_app; eauto | apply Forall_app; auto].
    + destruct (IH v0 v Hrest H2) as [p' [Hp'path Hp'for]].
      exists (a :: p').
      split; [eapply valid_epath_cons; eauto | constructor; auto]. 
      apply swap_cons_contains_old; auto. 
Qed.

Lemma Forall_rev_any :
  forall (A : Type) (Q : A -> Prop) (l : list A),
    Forall Q l ->
    Forall Q (rev l).
Proof.
  intros A Q l Hfor.
  rewrite Forall_forall.
  intros x Hinx.
  apply Forall_forall with (x := x) in Hfor.
  - exact Hfor.
  - apply in_rev.
    exact Hinx.
Qed.

Lemma chosen_path_disconnects_after_removal_from_spanning_tree :
  forall elist e e',
    NoDup elist ->
    is_spanning_tree elist ->
    chosen_path_disconnects_after_removal e e' elist.
Proof.
  intros elist e e' Hnd_elist Hspan.
  unfold chosen_path_disconnects_after_removal.
  intros u v p1 p2 y1 y2 Hstep_new Hpre Hstep_old Hpost Hnd_path Hfor_path Hreach_removed.
  destruct Hspan as [_ [_ Hacyc]].
  destruct Hreach_removed as [q [Hqpath Hqfor_removed]].
  pose proof (Nodup_split_constructors p1 p2 e' Hnd_path) as [Hnotin1 Hnotin2].
  apply Forall_app in Hfor_path.
  destruct Hfor_path as [Hfor1 Hfor_rest].
  inversion Hfor_rest as [|e0 p2' He'in_path Hfor2]; subst e0 p2'.
  assert (Hfor1_neq : Forall (fun x => In x elist /\ x <> e') p1).
  { eapply Forall_edge_set_neq_of_notin; eauto. }
  assert (Hfor2_neq : Forall (fun x => In x elist /\ x <> e') p2).
  { eapply Forall_edge_set_neq_of_notin; eauto. }
  assert (Hqfor_neq : Forall (fun x => In x elist /\ x <> e') q).
  { eapply Forall_remove_once_old_neq; eauto. }
  assert (Hmid_path : valid_epath g y2 (p2 ++ rev q ++ p1) y1).
  {
    rewrite app_assoc.
    eapply valid_epath_app.
    - eapply valid_epath_app.
      + exact Hpost.
      + apply valid_epath_rev.
        exact Hqpath.
    - exact Hpre.
  }
  assert (Hmid_for_neq : Forall (fun x => In x elist /\ x <> e') (p2 ++ rev q ++ p1)).
  {
    rewrite app_assoc.
    rewrite Forall_app.
    split.
    - rewrite Forall_app.
      split.
      + exact Hfor2_neq.
      + apply Forall_rev_any.
        exact Hqfor_neq.
    - exact Hfor1_neq.
  }
  destruct (valid_epath_simple_preserve_Forall
              (fun x => In x elist /\ x <> e') y2 (p2 ++ rev q ++ p1) y1
              Hmid_path Hmid_for_neq)
    as [q' [[Hq'_nd Hq'_path] Hq'_for_neq]].
  assert (Hq'_for : Forall (fun x => In x elist) q').
  {
    rewrite Forall_forall in *.
    intros x Hinx.
    destruct (Hq'_for_neq x Hinx) as [Hx _].
    exact Hx.
  }
  assert (~ In e' q') as Hq'_notin.
  {
    intro Hin.
    rewrite Forall_forall in Hq'_for_neq.
    destruct (Hq'_for_neq e' Hin) as [_ Hneq].
    exact (Hneq eq_refl).
  }
  apply Hacyc.
  exists y1, (e' :: q').
  split.
  - discriminate.
  - split.
    + split.
      * eapply valid_epath_cons; eauto.
      * constructor; auto.
    + constructor; auto.
Qed.

Lemma swap_reconnects_removed_edge_from_path_split :
  forall e e' elist u v p1 p2 y1 y2,
    step_aux g e u v ->
    valid_epath g u p1 y1 ->
    step_aux g e' y1 y2 ->
    valid_epath g y2 p2 v ->
    NoDup (p1 ++ e' :: p2) ->
    Forall (fun x => In x elist) (p1 ++ e' :: p2) -> 
    exists p, valid_epath g y1 p y2 /\ Forall (fun x => In x (swap_cons e e' elist)) p.
Proof.
  intros e e' elist u v p1 p2 y1 y2 Hstep_new Hpre Hstep_old Hpost Hnodup Hfor.
  pose proof (Nodup_split_constructors p1 p2 e' Hnodup) as [Hnotin1 Hnotin2].
  apply Forall_app in Hfor.
  destruct Hfor as [Hfor1 Hforrest].
  inversion Hforrest as [|x xs Hfor_e' Hfor2]; subst.
  assert (Forall (fun x => In x (swap_cons e e' elist)) p1) as Hfor1_swap.
  {
    rewrite Forall_forall.
    intros a Ha.
    apply swap_cons_contains_old.
    - intro Heq.
      apply Hnotin1.
      subst a.
      exact Ha.
    - apply Forall_forall with (x := a) in Hfor1; auto.
  }
  assert (Forall (fun x => In x (swap_cons e e' elist)) p2) as Hfor2_swap.
  {
    rewrite Forall_forall.
    intros a Ha.
    apply swap_cons_contains_old.
    - intro Heq.
      apply Hnotin2.
      subst a.
      exact Ha.
    - apply Forall_forall with (x := a) in Hfor2; auto.
  }
  assert (exists puy1, valid_epath g u puy1 y1 /\ Forall (fun x => In x (swap_cons e e' elist)) puy1) as Huy1.
  { eapply valid_epath_Forall_reachable_in_eset; eauto. }
  assert (exists p2y2, valid_epath g y2 p2y2 v /\ Forall (fun x => In x (swap_cons e e' elist)) p2y2) as Hy2v.
  { eapply valid_epath_Forall_reachable_in_eset; eauto. }
  assert (exists p1y1, valid_epath g y1 p1y1 u /\ Forall (fun x => In x (swap_cons e e' elist)) p1y1) as Hy1u.
  { destruct Huy1 as [puy1 [Huy1path Huy1for]].
    exists (rev puy1).
    split; [apply valid_epath_rev; exact Huy1path | apply Forall_rev_any; exact Huy1for]. }
  assert (exists p2v, valid_epath g v p2v y2 /\ Forall (fun x => In x (swap_cons e e' elist)) p2v) as Hvy2.
  { destruct Hy2v as [p2y2 [Hy2vpath Hy2vfor]].
    exists (rev p2y2).
    split; [apply valid_epath_rev; exact Hy2vpath | apply Forall_rev_any; exact Hy2vfor]. }
  assert (exists puv, valid_epath g u puv v /\ Forall (fun x => In x (swap_cons e e' elist)) puv) as Huv.
  {
    exists (e :: nil).
    split; [eapply valid_epath_single; eauto | constructor].
    apply swap_cons_contains_new.
    constructor.
  }
  destruct Hy1u as [p1y1 [Hy1upath Hy1ufor]].
  destruct Huv as [puv [Huvpath Huvfor]].
  destruct Hvy2 as [p2v [Hvy2path Hvy2for]].
  exists (p1y1 ++ puv ++ p2v).
  split. 
  * eapply valid_epath_app; [eauto|eapply valid_epath_app; eauto]. 
  * apply Forall_app; split; [|apply Forall_app; split]; auto.
Qed.

Lemma swap_reconnects_removed_edge_fixed_from_path_split :
  forall e e' elist u v p1 p2 y1 y2,
    step_aux g e u v ->
    valid_epath g u p1 y1 ->
    step_aux g e' y1 y2 ->
    valid_epath g y2 p2 v ->
    NoDup (p1 ++ e' :: p2) ->
    Forall (fun x => In x elist) (p1 ++ e' :: p2) ->
    swap_reconnects_removed_edge_fixed e e' elist.
Proof.
  intros e e' elist u v p1 p2 y1 y2 Hstep_new Hpre Hstep_old Hpost Hnodup Hfor u' v' Hstep_old'.
  pose proof (swap_reconnects_removed_edge_from_path_split e e' elist u v p1 p2 y1 y2
                Hstep_new Hpre Hstep_old Hpost Hnodup Hfor) as Hreach.
  pose proof (step_aux_unique_undirected g e' y1 y2 u' v' g_valid Hstep_old Hstep_old') as Huniq.
  destruct Huniq as [[Hu' Hv'] | [Hu' Hv']].
  - subst u' v'.
    exact Hreach.
  - subst u' v'. 
    destruct Hreach as [p [Hpath' Hfor']]. 
    exists (rev p); split; 
    [apply valid_epath_rev; exact Hpath' | 
    apply Forall_rev_any; exact Hfor'].
Qed.

Lemma swap_connectivity_from_reconnect_fixed :
  forall e e' elist,
    is_spanning_tree elist ->
    swap_reconnects_removed_edge_fixed e e' elist ->
    spans_all_vertices (swap_cons e e' elist).
Proof.
  intros e e' elist [_ [Hspan _]] Hreconn u v Huvalid Hvvalid.
  pose proof (Hspan u v Huvalid Hvvalid) as Holdreach.
  destruct Holdreach as [p [Hpath Hfor]].
  eapply valid_epath_transfer_to_swap_fixed; eauto.
Qed.

Lemma cycle_in_swap_must_use_new :
  forall e e' elist x p,
    acyclic_eset elist ->
    p <> nil ->
    is_simple_epath g x p x ->
    Forall (fun x => In x (swap_cons e e' elist)) p ->
    In e p.
Proof.
  intros e e' elist x p Hacyc Hpnonempty [Hnodup Hpath] Hfor.
  destruct (classic (In e p)) as [Hin | Hnotin]; auto.
  exfalso.
  apply Hacyc.
  exists x, p.
  split; [exact Hpnonempty |].
  split; [split; assumption |].
  eapply Forall_forall.
  intros a Ha.
  eapply (remove_once_in_elim _ e').
  eapply (edge_in_swap_not_new_removed e).
  - rewrite Forall_forall in *; auto.
  - unfold not; intros; subst; auto.
Qed.

Lemma swap_acyclicity_from_new_edge_cycle_free_fixed :
  forall e e' elist,
    acyclic_eset elist ->
    swap_keeps_new_edge_cycle_free_fixed e e' elist ->
    acyclic_eset (swap_cons e e' elist).
Proof.
  intros e e' elist Hold_acyc Hcyclefree.
  unfold acyclic_eset.
  intros [x [p [Hpnonempty [[Hpath Hnodup] Hfor]]]].
  pose proof (cycle_in_swap_must_use_new e e' elist x p Hold_acyc Hpnonempty (conj Hpath Hnodup) Hfor) as Hin.
  apply in_split in Hin.
  destruct Hin as [p1 [p2 Hp]].
  subst p. 
  apply valid_epath_app_inv in Hpath as [u [Hpre Hsuf]].
  apply valid_epath_cons_inv in Hsuf as [v [Hstep Hpost]].
  assert (~ In e (p2 ++ p1)) as Hnotin_rest.
  {
    pose proof (Nodup_split_constructors p1 p2 e Hnodup) as [Hnotin1 Hnotin2].
    rewrite in_app_iff; tauto.
  }
  assert (Forall (fun x => In x (remove_once e' elist)) (p2 ++ p1)) as Hfor_removed.
  {
    apply Forall_app.
    apply Forall_app in Hfor.
    destruct Hfor as [Hleft Hright].
    inversion Hright; subst.
    split.
    - eapply Forall_swap_removed_if_not_new; eauto.
      intros Hinp2.
      apply Hnotin_rest.
      rewrite in_app_iff; auto.
    - eapply Forall_swap_removed_if_not_new; eauto.
      intros Hinp1.
      apply Hnotin_rest.
      rewrite in_app_iff; auto.
  }
  pose proof (valid_epath_app _ _ _ _ _ _ Hpost Hpre) as Hcycle_rest.
  pose proof (valid_epath_Forall_reachable_in_eset
                (fun x => In x (remove_once e' elist)) v (p2 ++ p1) u
                Hcycle_rest Hfor_removed) as Hreach_removed.
  exfalso.
  eapply (Hcyclefree u v); eauto. 
  destruct Hreach_removed as [p' [Hpath' Hfor']].
  exists (rev p'); split; [apply valid_epath_rev; exact Hpath' | apply Forall_rev_any; exact Hfor'].
Qed.

Lemma swap_spanning_tree_from_fixed_graph_side :
  forall e e' elist,
    evalid g e ->
    is_spanning_tree elist ->
    swap_reconnects_removed_edge_fixed e e' elist ->
    swap_keeps_new_edge_cycle_free_fixed e e' elist ->
    is_spanning_tree (swap_cons e e' elist).
Proof.
  intros e e' elist Hevalid Hspan Hreconn Hcyclefree.
  unfold is_spanning_tree in *.
  destruct Hspan as [Holdvalid [Hconn Holdacyc]].
  split.
  - intros x Hin.
    eapply swap_cons_evalid; eauto.
  - split.
    + eapply swap_connectivity_from_reconnect_fixed.
      * split; [exact Holdvalid | split; [exact Hconn | exact Holdacyc]].
      * exact Hreconn.
    + eapply swap_acyclicity_from_new_edge_cycle_free_fixed.
      * exact Holdacyc.
      * exact Hcyclefree.
Qed.

End prim.
