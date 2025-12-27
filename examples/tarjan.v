Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.directed.rootedtree.
Require Import GraphLib.directed.dfstree.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.undirected.undirected_basic.
Require Import GraphLib.Syntax.
Require Import MaxMinLib.MaxMin MaxMinLib.Interface.
Require Import SetsClass.SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Arith.Arith.

Local Open Scope sets_scope.

Record OriginalGraphType {V E: Type} := {
  original_vvalid : V -> Prop;
  original_step: E -> Prop;
  original_step_fst: E -> V;
  original_step_snd: E -> V;
  original_listV: list V;
}.

Arguments OriginalGraphType _ _ : clear implicits.

Record OriginalGraphProp {V E: Type} (origin: OriginalGraphType V E): Prop := {
  original_step_fst_valid: forall e, origin.(original_step) e -> origin.(original_vvalid) (origin.(original_step_fst) e);
  original_step_snd_valid: forall e, origin.(original_step) e -> origin.(original_vvalid) (origin.(original_step_snd) e);
  original_finite_vertices: forall v, origin.(original_vvalid) v -> In v origin.(original_listV) ;
}.

Arguments OriginalGraphProp _ _ : clear implicits.

Record original_step_aux {V E: Type} (g: OriginalGraphType V E) (e: E) (x y: V): Prop:=
{ 
  original_vx : original_vvalid g x; 
  original_vy : original_vvalid g y;
  original_ve : original_step g e; 
  original_vH : (original_step_fst g e = x /\ original_step_snd g e = y) \/ 
  (original_step_fst g e = y /\ original_step_snd g e = x);
}.

#[export]Instance OriginalGraph_graph {V E: Type} : 
  Graph (OriginalGraphType V E) V E := {|
  graph_basic.vvalid := original_vvalid;
  graph_basic.evalid := original_step;
  graph_basic.step_aux := original_step_aux;
|}.

#[export]Instance OriginalGraph_gvalid {V E: Type} : 
  GValid (OriginalGraphType V E) :=
  @OriginalGraphProp V E.

#[export]Instance OriginalGraph_stepvalid {V E: Type}: 
  StepValid (OriginalGraphType V E) V E.
Proof.
  split; intros;
  destruct H; 
  destruct original_vH0; 
  destruct H as [? ?]; auto;
  repeat split; auto.
Qed.

#[export]Instance OriginalGraph_noemptyedge {V E: Type}: 
  NoEmptyEdge (OriginalGraphType V E) V E.
Proof.
  split; intros.
  exists (g.(original_step_fst V E) e), (g.(original_step_snd V E) e).
  repeat split; auto.
  apply original_step_fst_valid; auto.
  apply original_step_snd_valid; auto.
Qed.

#[export]Instance OriginalGraph_stepuniqueundirected {V E: Type}: 
  StepUniqueUndirected (OriginalGraphType V E) V E.
Proof.
  split; intros.
  destruct H0.
  destruct H1.
  destruct original_vH0; destruct original_vH1;
  destruct H; destruct H0; subst; firstorder. 
Qed.

#[export]Instance OriginalGraph_undirected {V E: Type}: 
  UndirectedGraph (OriginalGraphType V E) V E.
Proof.
  split; intros; auto.
  destruct H.
  destruct original_vH0; auto; 
  split; tauto. 
Qed.

#[export]Instance Original_finitegraph {V E: Type}:
  FiniteGraph (OriginalGraphType V E) V E. 
Proof.
  refine {|graph_basic.listV := original_listV; |}.
  intros.
  apply original_finite_vertices; auto.
Defined.


Record RootedTreeType {V E: Type}:=
{
  vset: V -> Prop;
  theroot: V;
  parent: V -> V;
  edge: V -> option E;
  listV: list V;
}.

Arguments RootedTreeType _ _ : clear implicits.

Notation "tree '.(vset)'" := (vset tree) (at level 1).
Notation "tree '.(root)'" := (theroot tree) (at level 1).
Notation "tree '.(parent)'" := (parent tree) (at level 1).
Notation "tree '.(edge)'" := (edge tree) (at level 1).

Record RootedTreeProp {V E: Type} (rt: RootedTreeType V E):=
{
  root_no_edge: rt.(edge) (rt.(root)) = None;
  edge_some: forall v, rt.(vset) v -> v <> rt.(root) -> exists e, rt.(edge) v = Some e;
  edge_unique: forall v1 v2, rt.(vset) v1 -> rt.(vset) v2 -> rt.(edge) v1 = rt.(edge) v2 -> v1 = v2;
  root_valid: rt.(vset) rt.(theroot);
  parent_valid: forall v, rt.(vset) v -> rt.(vset) (rt.(parent) v);
  path_exist: forall v, rt.(vset) v -> clos_refl_trans (fun x y => rt.(parent) y = x) rt.(theroot) v;
  finite_vertices: forall v, rt.(vset) v -> In v rt.(listV) ;
}.

Arguments RootedTreeProp _ _ : clear implicits.

Definition rt_vvalid {V E: Type} (g: RootedTreeType V E) (v: V): Prop :=
  g.(vset) v.

Definition rt_evalid {V E: Type} (g: RootedTreeType V E) (e: E): Prop :=
  exists v, g.(vset) v /\ g.(edge) v = Some e.

Record rt_step_aux {V E: Type} (g: RootedTreeType V E) (e: E) (x y: V): Prop := 
{ 
  vx : g.(vset) x;
  vy : g.(vset) y;
  ve : g.(edge) y = Some e;
  vp : g.(parent) y = x
}.

#[export]Program Instance Rootedtree_graph {V E: Type}:
  graph_basic.Graph (RootedTreeType V E) V E := {
  vvalid := rt_vvalid ;
  evalid := rt_evalid ;
  step_aux := rt_step_aux;
}.

#[export]Instance Rootedtree_gvalid {V E: Type}:
  graph_basic.GValid (RootedTreeType V E) :=
  @RootedTreeProp V E.

#[export]Instance Rootedtree_stepvalid {V E: Type}: 
  StepValid (RootedTreeType V E) V E.
Proof.
  split; intros; destruct H; auto.
  exists y; auto.
Qed. 

#[export]Instance Rootedtree_noemptyedge {V E: Type} : 
  graph_basic.NoEmptyEdge (RootedTreeType V E) V E.
Proof.
  split; intros.
  destruct H0 as [v [? ?]].
  exists (parent g v), v; repeat split; auto.
  apply parent_valid; auto.
Qed.

#[export]Instance Rootedtree_directedgragh {V E: Type}: 
  graph_basic.StepUniqueDirected (RootedTreeType V E) V E .
Proof.
  split; intros ? ? ? ? ? ? HH ? ?.
  destruct H.
  destruct H0.
  rewrite <- ve0 in ve1.
  eapply edge_unique in ve1; eauto. 
  subst y2.
  rewrite <- vp1; subst x2.
  split; auto.
Qed.

#[export]Instance RootedTree_finitegraph {V E: Type}:
  graph_basic.FiniteGraph (RootedTreeType V E) V E. 
Proof.
  refine {|graph_basic.listV:= listV;|}.
  intros; apply finite_vertices; auto.
Defined.
  
#[export]Instance Rootedtree_prop {V E: Type} :
  RootedTree (RootedTreeType V E) V E.
Proof.
  refine {|root := theroot;|}.
  - intros; apply root_valid; auto.
  - intros g x HH H.
  apply path_exist in H as H0; auto. 
  revert H; rename H0 into H.
  remember g.(root) as r. 
  induction_n1 H. 
  reflexivity.
  destruct (classic (x = r)).
  subst x; reflexivity.
  eapply parent_valid in H0 as Hy.
  rewrite H1 in Hy.
  apply IHrt in Hy as ?; auto.
  etransitivity; eauto.
  unfold reachable.
  apply step_rt.
  apply edge_some in H0 as H4; auto.
  destruct H4 as [e H4].
  exists e; repeat split; auto.
  subst r; auto.
  auto. 
  - intros g x HH. 
  unfold not; intros.
  destruct H as [e ?].
  destruct H.
  erewrite root_no_edge in ve0; eauto.
  inversion ve0.
  - intros g ? ? ? ? ? HH ? ?.  
  destruct H.
  destruct H0.
  rewrite ve0 in ve1.
  inversion ve1; subst e2.
  reflexivity.
Defined.


#[export]Instance simple_graph{V E: Type}: 
  graph_basic.SimpleGraph (RootedTreeType V E) V E.
Proof.
  split; intros.
  - eapply father_eunique; eauto.
  - unfold not; intros H0.
    apply step_trivial in H0.
    eapply no_edge_refl; eauto.
    Unshelve. auto.
Qed.

Section TARJAN.
Context {V E: Type}
        (g: OriginalGraphType V E)
        (origin_gvalid: OriginalGraph_gvalid g)
        (dfstree: RootedTreeType V E)
        (tree_valid: Rootedtree_gvalid dfstree)
        (RootedTree_finitegraph: FiniteGraph (RootedTreeType V E) V E) (*hope to derived from sub*)
        (sub: subgraph dfstree g)
        (dfn: V -> nat)
        (dfnv: dfn_valid dfstree dfn)
        (low: V -> nat).

Notation theroot := dfstree.(root).
Notation subtree := (offspring dfstree).
Notation son := (step dfstree).

Definition no_cross_edge := 
  forall x y, reachable g theroot x -> reachable g theroot y -> step g x y -> reachable dfstree x y \/ reachable dfstree y x.

Definition reachable_visited: Prop :=
  forall u, reachable g theroot u -> vvalid dfstree u.

Context {nocross: no_cross_edge}
        {reacheable_is_visited: reachable_visited}.


Section LOW. 

(* Definition step_without_tree (x y: V): Prop := 
  exists e, step_aux dfstree e x y /\ ~ evalid dfstree e.

Definition subtree_step (y: V): (V -> Prop) := 
  fun w => exists z, 
    subtree y z /\ step_without_tree z w. 

Definition low_tree (y: V) : V -> Prop := subtree y ∪ subtree_step y.

(* v的low值满足定义 *)
Definition is_low_v (v: V): nat -> Prop :=
  fun lowv => 
    min_value_of_subset Nat.le (low_tree v) dfn lowv.

Definition is_low (fun_low: V -> nat): Prop :=
  forall v, vvalid dfstree v -> is_low_v v (fun_low v). 

(* 函数fun_low在v上满足local性质 *)
Definition low_valid_v (v: V) (fun_low: V -> nat): Prop :=
  min_value_of_subset Nat.le
  (min_value_of_subset Nat.le (son v) fun_low ∪ 
  min_value_of_subset Nat.le (step_without_tree v ∪ [v]) dfn)
  id (fun_low v).


Definition low_valid (fun_low: V -> nat): Prop := 
  forall v, vvalid dfstree v -> low_valid_v v fun_low.


Lemma reachable_subtree:
  forall u, reachable g theroot u -> subtree theroot u.
Proof.
  intros.
  apply reacheable_is_visited in H.
  destruct (classic (theroot = u)) as [|neq_root].
  - subst; reflexivity.
  - eapply root_is_root in H; eauto.
Qed.

Lemma leaf_subree (u: V):
  isleaf dfstree u ->
  subtree u == [u].
Proof.
  intros.
  split; intros.
  - destruct (classic (u = a)); auto.
  eapply real_offspring in H0; eauto.
  destruct H0 as [z []].
  exfalso; eapply H; eauto.
  - sets_unfold in H0; subst.
  reflexivity.
  Unshelve. auto.
Qed.

Lemma subtree_decompose (u: V): 
  subtree u ==  
  [u] ∪ 
  (fun w => exists z, son u z /\ subtree z w).
Proof. 
  split; intros. 
  - destruct (classic (u = a)). 
    * subst; left; reflexivity. 
    * eapply real_offspring in H0 as [? []]; eauto . 
      right; exists x; auto. 
  - destruct H as [|[? []]].
    * sets_unfold in H; subst; reflexivity. 
    * eapply step_reachable_reachable; eauto. 
  Unshelve. auto.  
Qed.

Lemma subtree_step_decompose (y : V) (Hvy: vvalid dfstree y): 
  subtree_step y  == 
  step_without_tree y ∪
  (fun w => exists z, son y z /\ subtree_step z w).
Proof.
  split; intros.
  - destruct H as [z [? ?]].
    destruct (classic (y = z)); [subst; left; auto|right]. 
    eapply real_offspring in H1 as [w [? ?]]; eauto. 
    exists w; split; auto. 
    exists z; split; auto. 
  - destruct H as [|[w [? [z []]]]]. 
    + exists y; split; auto. 
      reflexivity. 
    + exists z; split; auto. 
      eapply step_reachable_reachable; eauto. 
  Unshelve. auto.
Qed. 

Theorem low_tree_decompose (y: V) (Hvy: vvalid dfstree y):
  low_tree y == (fun w => exists z, son y z /\ low_tree z w) ∪ step_without_tree y ∪ [y].
Proof.
  unfold low_tree. 
  rewrite subtree_decompose. 
  rewrite Sets_union_assoc.
  
  rewrite Sets_union_comm. 
  apply Sets_union_congr; [|reflexivity]. 
  split; intros.
  - destruct H as [[z []]|[z []]]. 
    + left; exists z; split; auto. 
      left; auto. 
    + destruct (classic (y = z)); [subst|].
      * right; auto. 
      * eapply real_offspring in H as [w []]; eauto. 
        left; exists w; split; auto.
        right; exists z; split; auto.
  - destruct H as [[z [? [|[w []]]]]|]. 
    + left; exists z; split; auto. 
    + right; exists w; split; auto. 
      eapply step_reachable_reachable; eauto.
    + right; exists y; split; auto. 
      reflexivity. 
  Unshelve. auto. 
Qed.

Lemma low_valid_induction (v: V) (fun_low: V -> nat)
  (IHv: forall w, son v w -> is_low_v w (fun_low w)): 
  min_value_of_subset Nat.le (son v) fun_low == 
  min_value_of_subset Nat.le ((fun w => exists z, son v z /\ low_tree z w)) dfn.
Proof. 
  intros; split; intros.
  * destruct H as [z [[] ?]].
    pose proof IHv z H as [? [[] ?]].
    exists x; split.
    ** split. 
       { exists z; split; auto. } 
       { intros. 
         destruct H5 as [z0 []].
         pose proof IHv z0 H5 as [? [[] ?]]. 
         pose proof H0 z0 H5.  
         pose proof H8 b H6.
         lia. } 
    ** lia. 
  * destruct H as [? [[] ?]].
    destruct H as [? []]. 
    exists x0; split.
    ** split; auto. 
       intros. 
       destruct (IHv x0 H) as [? [[] ?]]. 
       pose proof H5 x H2. 
       pose proof IHv b H3 as [? [[] ?]]. 
       rewrite <- H6, <- H10. 
       pose proof H5 x0 (ltac:(left; reflexivity)). 
       pose proof H9 b (ltac:(left; reflexivity)). 
       pose proof H0 x2 (ltac:(exists b; split; auto)). 
       lia.
    ** subst. 
       unfold ge in *. 
       pose proof IHv x0 H as [? [[] ?]].
       pose proof H3 x H2. 
       pose proof H0 x1 (ltac:(exists x0; split; auto)). 
       lia.
Qed. 

Lemma low_valid_induction_is_low 
  (v: V) 
  (fun_low: V -> nat) 
  (Hv: vvalid dfstree v)
  (IHv: forall w, son v w -> is_low_v w (fun_low w)):
  low_valid_v v fun_low ->
  is_low_v v (fun_low v).
Proof.
  intros.
  unfold low_valid_v in H. 
  rewrite low_valid_induction in H; auto.
  apply min_union_iff in H.
  unfold is_low_v.
  rewrite low_tree_decompose; auto. 
  rewrite Sets_union_assoc.
  auto.
Qed.

Lemma low_valid_implies_is_low 
  (fun_low: V -> nat): 
  low_valid fun_low ->
  is_low fun_low.
Proof.
  intros low_valid.
  unfold is_low.
  pose proof @rooted_tree_induction_bottom_up 
  (RootedTreeType V E) V E _ _ _ _ _ dfstree tree_valid _
  (fun v => vvalid dfstree v -> is_low_v v (fun_low v)).
  apply H.
  intros.
  apply low_valid_induction_is_low; auto.
  intros; apply H0; auto. 
  destruct H2; eapply step_vvalid2; eauto.
Qed. *)

(* low_valid: satisfied after program execution *)
(* is_low: definition of low based on dfn value *)

Definition subtree_step (y: V): (V -> Prop) :=
  fun w => 
    match dfstree.(edge) y with
    | Some e =>
      exists z, subtree y z /\ step_without g e z w
    | None =>
      reachable dfstree y w
  end.

Definition step_without_parent_edge (x: V) : (V -> Prop) :=
  fun y : V => 
    match dfstree.(edge) x with
    | Some e =>
      step_without g e x y
    | None =>
      step g x y
    end.

Definition low_tree (y: V) : V -> Prop := subtree y ∪ subtree_step y.

(* v的low值满足定义 *)
Definition is_low_v (v: V): nat -> Prop :=
  fun lowv => 
    min_value_of_subset Nat.le (low_tree v) dfn lowv.

Definition is_low (fun_low: V -> nat): Prop :=
  forall v, vvalid dfstree v -> is_low_v v (fun_low v). 

(* 函数fun_low在v上满足local性质 *)
Definition low_valid_v (v: V) (fun_low: V -> nat): Prop :=
  min_value_of_subset Nat.le
  (min_value_of_subset Nat.le (son v) fun_low ∪ 
  min_value_of_subset Nat.le (step_without_parent_edge v ∪ [v]) dfn)
  id (fun_low v).


Definition low_valid (fun_low: V -> nat): Prop := 
  forall v, vvalid dfstree v -> low_valid_v v fun_low.


Lemma reachable_subtree:
  forall u, reachable g theroot u -> subtree theroot u.
Proof.
  intros.
  apply reacheable_is_visited in H.
  destruct (classic (theroot = u)) as [|neq_root].
  - subst; reflexivity.
  - eapply root_is_root in H; eauto.
Qed.

Lemma leaf_subree (u: V):
  isleaf dfstree u ->
  subtree u == [u].
Proof.
  intros.
  split; intros.
  - destruct (classic (u = a)); auto.
  eapply real_offspring in H0; eauto.
  destruct H0 as [z []].
  exfalso; eapply H; eauto.
  - sets_unfold in H0; subst.
  reflexivity.
  Unshelve. auto.
Qed.

Lemma root_low_tree: 
  low_tree theroot == subtree theroot.
Proof.
  split; intros.
  - destruct H; auto.
  unfold subtree_step in H.
  destruct (dfstree.(edge) theroot) as [e|] eqn:Heq. 
  * exfalso; rewrite root_no_edge in Heq; auto. 
  inversion Heq.
  * auto.
  - left; auto.
Qed.

Lemma low_tree_original_reachable (x y: V):
  low_tree x y -> reachable g x y.
Proof.
  intros.
  destruct H.
  - revert H. eapply sub_reachable; eauto.
  - unfold subtree_step in H. 
  destruct (dfstree.(edge) x) as [e|] eqn:Heq.
  * destruct H as [z []].
  destruct H0 as [e0 []].
  unfold reachable.
  transitivity_n1 z.
  ** revert H. eapply sub_reachable; eauto.
  ** eapply step_trivial; eauto.
  * revert H. eapply sub_reachable; eauto.
Qed.


Lemma root_low_tree_construct:
  (fun w => exists z, son theroot z /\ low_tree z w) ∪ step_without_parent_edge theroot ∪ [theroot] == subtree theroot.
Proof.
  split; intros.
  - destruct H as [[|]|].
  * destruct H as [z []].
  apply reachable_subtree.
  unfold reachable. 
  transitivity_1n z.
  ** revert H. eapply sub_step'; eauto.
  ** apply low_tree_original_reachable; auto.
  * unfold step_without_parent_edge in H.
  destruct (dfstree.(edge) theroot) as [e|] eqn:Heq. 
  ** exfalso; rewrite root_no_edge in Heq; auto.
  inversion Heq.
  ** apply reachable_subtree.
  apply step_rt; auto.
  * sets_unfold in H; subst.
  reflexivity.
  - destruct (classic (theroot = a)) as [|neq_root].
  * subst; right; reflexivity.
  * left; left.
  eapply real_offspring in neq_root; eauto.
  destruct neq_root as [z []].
  exists z; split; auto. 
  left; auto.
  Unshelve. auto.
Qed.

Lemma edge_step_aux (u: V) (e: E):
  vvalid dfstree u ->
  dfstree.(edge) u = Some e ->
  exists x, step_aux dfstree e x u.
Proof.
  intros He.
  exists (dfstree.(parent) u).
  split; auto.
  apply parent_valid; auto.
Qed.
  
Lemma subtree_decompose (u: V): 
  subtree u ==  
  [u] ∪ 
  (fun w => exists z, son u z /\ subtree z w).
Proof. 
  split; intros. 
  - destruct (classic (u = a)). 
    * subst; left; reflexivity. 
    * eapply real_offspring in H0 as [? []]; eauto . 
      right; exists x; auto. 
  - destruct H as [|[? []]].
    * sets_unfold in H; subst; reflexivity. 
    * eapply step_reachable_reachable; eauto. 
  Unshelve. auto.  
Qed.

Lemma construct_low_tree (y: V) (Hvy: vvalid dfstree y):
  low_tree y == (fun w => exists z, son y z /\ low_tree z w) ∪ step_without_parent_edge y ∪ [y].
Proof.
  destruct (classic (y = theroot)) as [|neq_root].
  1: { rewrite H. erewrite root_low_tree. rewrite root_low_tree_construct. reflexivity. }
  split; intros.
  - destruct H. 
    (* subtree *)
    * destruct_equality_impl a y.
      (* local *)
      + subst; right; reflexivity.
      (* son *)
      + left; left. 
        eapply real_offspring in H; eauto.
        destruct H as [z [? ?]]; exists z; split; auto.
        left; auto.
    (* subtree_step *)
    * unfold subtree_step in H.
      apply edge_some in Hvy as [e Hy]; auto.
      rewrite Hy in H.
      destruct H as [z [? ?]].
      destruct_equality_impl z y.
      (* local *)
      + subst; left; right.
        unfold step_without_parent_edge; rewrite Hy.
        auto.
      + destruct_equality_impl a y. 
         (* most special: back edge = tree edge reversed, but solved by ∪ [y]  *)
        1: { right; reflexivity. }
         (* low tree equals when back edge != tree edge, complexed categorised discussion  *)
        left; left. 
        eapply real_offspring in H; eauto.
        destruct H as [w [? ?]]; exists w; split; auto.
        right.
        unfold subtree_step.
        pose proof H as H2.
        apply step_vvalid in H2 as [_ Hw].
        assert (w <> theroot). 
        { unfold not; intros; subst w.
          eapply root_no_father; eauto. }
        apply edge_some in H2; auto.
        destruct H2 as [e2 H2].
        rewrite H2.
        exists z; split; auto.
        apply edge_step_aux in H2 as [x]; auto.
        apply step_trivial in H2 as H5. 
        unshelve eapply father_vunique in H; eauto; subst.
        clear H5.
        destruct H0 as [e1 [? ?]]. 
        exists e1; split; auto. 
        unfold not; intros; subst e1.
        apply sub in H2 as H6. 
        eapply step_aux_unique_undirected in H as H7; eauto.
        destruct H7 as [H7 | H7]; 
        destruct H7; subst;
        exfalso; auto. 
  - destruct H as [[]|].
    (* son *)
    * destruct H as [x [? ?]]. destruct H0. 
      (* subtree *)
      + left. unfold offspring in *; unfold reachable in *.
        transitivity_1n x; auto. 
      (* subtree_step *)
      + right. pose proof H as [e He].
        assert (x <> theroot). 
        { unfold not; intros; subst x;
        eapply root_no_father; eauto. }
        pose proof H as H2.
        eapply step_vvalid in H2 as [].
        apply edge_some in neq_root as [ey Hy]; auto.
        apply edge_some in H1 as [ex Hx]; auto.
        unfold subtree_step in *.
        rewrite Hy. rewrite Hx in H0. 
        destruct H0 as [z []].
        exists z; split; auto.
        unfold offspring, reachable; 
        transitivity_1n x; auto.
        destruct H1 as [eza [? ?]].
        exists eza; split; auto.
        unfold not; intros; subst eza.
        apply edge_step_aux in Hy as [w]; auto.
        apply sub in H5 as H6. 
        eapply step_aux_unique_undirected in H1 as H7; eauto.
        (* two special cases: back edge = tree edge reversed or back edge = tree edge *)
        destruct H7 as [[] | []]; subst.
        (* back edge = tree edge reversed *)
        ++ apply step_trivial in H5, He.
           eapply offspring_not_father; 
           unfold offspring, reachable.  
           transitivity_1n x; eauto. auto. 
         (* back edge = tree edge *)
        ++ eapply offspring_not_father; eauto.
    (* local_step *)
    * right.
      apply edge_some in neq_root as [e Hy]; auto.
      unfold step_without_parent_edge in H;
      unfold subtree_step.
      rewrite Hy in *.
      exists y; split; auto.
      reflexivity.
    (* self *)
    * sets_unfold in H; subst.
      left; reflexivity.
  Unshelve. auto. auto. auto. auto.
Qed.

Lemma low_valid_induction (v: V) (fun_low: V -> nat)
  (IHv: forall w, son v w -> is_low_v w (fun_low w)): 
  min_value_of_subset Nat.le (son v) fun_low == 
  min_value_of_subset Nat.le ((fun w => exists z, son v z /\ low_tree z w)) dfn.
Proof. 
  intros; split; intros.
  * destruct H as [z [[] ?]].
    pose proof IHv z H as [? [[] ?]].
    exists x; split.
    ** split. 
       { exists z; split; auto. } 
       { intros. 
         destruct H5 as [z0 []].
         pose proof IHv z0 H5 as [? [[] ?]]. 
         pose proof H0 z0 H5.  
         pose proof H8 b H6.
         lia. } 
    ** lia. 
  * destruct H as [? [[] ?]].
    destruct H as [? []]. 
    exists x0; split.
    ** split; auto. 
       intros. 
       destruct (IHv x0 H) as [? [[] ?]]. 
       pose proof H5 x H2. 
       pose proof IHv b H3 as [? [[] ?]]. 
       rewrite <- H6, <- H10. 
       pose proof H5 x0 (ltac:(left; reflexivity)). 
       pose proof H9 b (ltac:(left; reflexivity)). 
       pose proof H0 x2 (ltac:(exists b; split; auto)). 
       lia.
    ** subst. 
       unfold ge in *. 
       pose proof IHv x0 H as [? [[] ?]].
       pose proof H3 x H2. 
       pose proof H0 x1 (ltac:(exists x0; split; auto)). 
       lia.
Qed. 

Lemma low_valid_induction_is_low 
  (v: V) 
  (fun_low: V -> nat) 
  (Hv: vvalid dfstree v)
  (IHv: forall w, son v w -> is_low_v w (fun_low w)):
  low_valid_v v fun_low ->
  is_low_v v (fun_low v).
Proof.
  intros.
  unfold low_valid_v in H. 
  rewrite low_valid_induction in H; auto.
  apply min_union_iff in H.
  unfold is_low_v.
  rewrite construct_low_tree; auto. 
  rewrite Sets_union_assoc.
  auto.
Qed.

Lemma low_valid_implies_is_low 
  (fun_low: V -> nat): 
  low_valid fun_low ->
  is_low fun_low.
Proof.
  intros low_valid.
  unfold is_low.
  pose proof @rooted_tree_induction_bottom_up 
  (RootedTreeType V E) V E _ _ _ _ _ dfstree tree_valid _
  (fun v => vvalid dfstree v -> is_low_v v (fun_low v)).
  apply H.
  intros.
  apply low_valid_induction_is_low; auto.
  intros; apply H0; auto. 
  destruct H2; eapply step_vvalid2; eauto.
Qed.


Lemma root_dfn_minimum: 
  forall x, min_value_of_subset Nat.le (subtree x) dfn (dfn x).
Proof.
  intros x.
  unfold min_value_of_subset; exists x; split; [split|].
  - unfold subtree.  
    sets_unfold. 
    reflexivity. 
  - intros; subst. 
    unfold subtree in H. 
    eapply dfn_valid_offspring; eauto; apply H.
    Unshelve. auto. 
  - reflexivity.
Qed.


Lemma low_valid1: is_low low -> 
  forall y z, vvalid dfstree y -> 
  reachable dfstree y z -> 
  low y <= dfn z.
Proof.
  intros H y z Hvy H0.
  unfold is_low in H.
  unfold low_tree in H.
  specialize (H y). 
  pose proof H Hvy. 
  unfold is_low_v in H1. 
  unfold low_tree in H1. 
  eapply min_exists_union_l; eauto.
Qed.

Lemma low_valid2: is_low low -> 
  forall x y z w e, step_aux dfstree e x y -> 
  reachable dfstree y z -> 
  step_without g e z w -> 
  low y <= dfn w.
Proof.
  intros H x y z w e H0 H1 H2.
  unfold is_low in H.
  unfold low_tree in H.
  specialize (H y).
  assert (Hvy: vvalid dfstree y) by (destruct H0; auto). 
  pose proof H Hvy. 
  unfold is_low_v in H3. 
  unfold low_tree in H3. 
  eapply min_exists_union_r with (f:=dfn) (P:=subtree y) (Q:=subtree_step y); eauto. 
  exists w; split; auto. 
  destruct (classic (y = theroot)) as [|neq_root].
  * subst y.
  unfold subtree_step.
  rewrite root_no_edge; auto.
  assert (reachable g theroot w).
  { unfold reachable.
  transitivity_n1 z. 
  revert H1; eapply sub_reachable; eauto.
  destruct H2 as [e0 []]; exists e0; auto. }
  apply reachable_subtree; auto.
  * assert (vvalid dfstree y) by (destruct H0; auto).
  apply edge_some in neq_root as [e0 Hy]; auto.
  unfold subtree_step.
  rewrite Hy.
  exists z; split; auto.
  eapply edge_step_aux in Hy; eauto.
  destruct Hy.
  eapply father_eunique in H0 as eq; eauto.
  subst e0; auto. 
Qed.

Lemma low_intros: is_low low -> 
  forall x y e, 
  vvalid dfstree y ->
  (exists z, reachable dfstree y z /\ low y = dfn z) \/ 
  (step_aux dfstree e x y -> exists z w, reachable dfstree y z /\ step_without g e z w /\ low y = dfn w).
Proof.
  intros H x y e Hvy.
  unfold is_low in H.
  unfold is_low_v in H.
  specialize (H y Hvy). 
  destruct H as [z [[]]].
  destruct H.
  - left. exists z; auto.
  - right. remember z as w; subst z.
    intros. unfold subtree_step in H.
    destruct (classic (y = theroot)) as [|neq_root].
    * exfalso. subst y. 
      apply step_trivial in H2.
      eapply root_no_father; eauto.
    * assert (vvalid dfstree y) by (destruct H1; auto).
      apply edge_some in neq_root as [e0 Hy]; auto.
      rewrite Hy in H.
      apply edge_step_aux in Hy as [x0 Hy]; auto.
      destruct H as [z []]. 
      exists z, w.
      repeat split; auto.
      eapply father_eunique in H2; eauto.
      subst; auto.
Qed. 

End LOW.

Context {low_valid: is_low low}.

Lemma low_dfn_ref : forall x,
  vvalid dfstree x -> low x <= dfn x.
Proof.
  intros.
  eapply low_valid1; eauto.
  reflexivity.
Qed.

Lemma white_reachable_aux: forall x y, 
  reachable g theroot x -> reachable g theroot y ->
  reachable_dfn_gt dfn (dfn x) g x y -> subtree x y.
Proof.
  intros x y Hx Hy H0.  
  unfold reachable_dfn_gt in H0.
  unfold reachable_tl in H0.
  remember (step_tl (fun t : V => dfn t >= dfn x) g) as P.
  induction_n1 H0.
  + reflexivity.
  + subst P. destruct H.
    assert (reachable g theroot x0) as Hx0. 
    { apply reachable_gt_reachable in H0. transitivity x; auto. }
    eapply nocross in H; eauto.
    destruct H.
    * etransitivity; eauto. 
    * destruct_equality_impl x y. reflexivity.
      eapply offspring_one_reachable with (x:=x)(y:=y)(z:=x0) in H as H2; eauto.
      destruct H2; [|auto].
      exfalso; auto.
      eapply @dfn_valid_offspring' with (dfn:=dfn) in H2; eauto.
      lia.
  Unshelve. auto.
Qed.

Lemma closed_offspring_aux: forall x y z w e,
  dfn x < low y ->
  step_aux dfstree e x y ->
  subtree y z -> 
  step_without g e z w -> 
  subtree y w.
Proof.
  intros. 
  destruct H2 as [e0 [H2 H3]].
  eapply low_valid2 with (w:=w) in H1 as Hlt; eauto.
  2: { unfold step_without. exists e0; auto. }
  apply step_trivial in H2.
  pose proof H2 as Hzw.
  assert (reachable g theroot z) as Hz. 
  {
    transitivity y. 
    * apply step_vvalid2 in H0.
      apply root_is_root in H0; auto.
      eapply sub_reachable; eauto.
    * eapply sub_reachable; eauto.
  }
  assert (reachable g theroot w) as Hw. 
  {
    transitivity z; auto.
    apply step_rt; auto. 
  }
  eapply nocross in H2; eauto.
  destruct H2.
  - etransitivity; eauto.
  - eapply offspring_one_reachable in H1 as H5; eauto.
    destruct H5; auto.
    destruct_equality_impl w y.
    eapply one_reachable_down_up in H4 as H6; eauto.
    eapply @dfn_valid_offspring with (dfn:= dfn) in H6; eauto.
    2: eapply step_trivial; eauto.
    lia.
  Unshelve. auto. auto.
Qed.

Lemma closed_offspring: forall x y z e,
  dfn x < low y ->
  step_aux dfstree e x y ->
  reachable_without g e y z -> 
  subtree y z.
Proof.
  intros.
  unfold reachable_without in H1.
  induction_n1 H1.
  - reflexivity.
  - unfold step_without in H2. 
    destruct H2 as [e0 [? ?]].
    eapply closed_offspring_aux; eauto.
    exists e0. split; auto.
Qed.

Lemma father_unreachable: forall x y e,
  dfn x < low y ->
  step_aux dfstree e x y ->
  ~ reachable_without g e y x.
Proof.
  unfold not; intros.
  eapply closed_offspring in H0 as H2; eauto.
  eapply step_trivial in H0 as H3; eauto.
  apply step_rt in H3.
  eapply offspring_partial_order in H3; eauto.
  subst y.
  eapply no_self_loop; eauto.
  Unshelve. auto. auto.
Qed.

Lemma offspring_step_ancestor: forall x y z w e,
  dfn x >= low y ->
  step_aux dfstree e x y ->
  reachable dfstree y z ->
  step_without g e z w ->
  low y = dfn w ->
  subtree w x.
Proof.
  intros x y z w e H1 H0 H H2 H3.
  assert (reachable g theroot x) as Hx.
  { 
    apply step_vvalid1 in H0.
    apply root_is_root in H0; auto.
    eapply sub_reachable; eauto.
  }
  assert (vvalid dfstree y) as Hvy by (apply H0).
  eapply step_trivial in H0; auto.
  destruct H2 as [e0 [H2 _]].
  eapply step_trivial in H2; auto.
  assert (reachable g theroot w) as Hw. 
  {
    transitivity z.
    transitivity y.
    * apply root_is_root in Hvy; auto.
      eapply sub_reachable; eauto.
    * eapply sub_reachable; eauto.
    * apply step_rt; auto. 
  }
  eapply white_reachable_aux; eauto.
  transitivity y. 
  transitivity z.
  - unfold reachable_dfn_gt.
    unfold reachable_tl.
    apply step_tl_rt.
    unfold step_tl.
    split; auto.
    eapply step_sym'; eauto.
    eapply @dfn_valid_offspring with (dfn:= dfn) in H as H4; eauto.
    pose proof low_dfn_ref y Hvy. 
    lia. 
  - eapply offspring_reachable_gt in H as H4; eauto.
    unfold reachable_dfn_gt in H4.
    apply sub_reachable_tl with (g2:=g) in H4; eauto.
    eapply reachable_gt_sym; eauto.
    * rewrite <- H3. 
    apply low_dfn_ref; auto.
    * assert (dfn y >= dfn w).
    rewrite <- H3. 
    apply low_dfn_ref; auto.
    eapply reachable_gt_mono; eauto.
  - unfold reachable_dfn_gt.
    unfold reachable_tl.
    transitivity_1n x; auto.
    2: reflexivity.
     split; auto.
    eapply @sub_step' with (g2:=g) in H0; eauto.
    eapply step_sym'; eauto.
    lia.
    Unshelve. auto. 
Qed.

Lemma tarjan: forall x y e, 
  step_aux dfstree e x y -> 
  (is_bridge g e <-> dfn x < low y).
Proof.
  intros x y e H0.
  assert (vvalid dfstree y) as Hvy by (apply H0).
  pose proof H0 as He.
  apply step_trivial in H0.
  split.
  - intros Hb; apply NNPP. unfold not at 1; intros. 
    intros. eapply Compare_dec.not_lt in H.
    pose proof H0 as [exy Hexy].
    eapply low_intros with (x := x)(y := y)(e := exy) in low_valid as H1; eauto.
    destruct H1.
    * destruct H1 as [z [? ?]].
    eapply dfnv in H0; eauto.
    eapply @dfn_valid_offspring with (dfn := dfn) in H1 as H3; eauto.
    lia.
    * pose proof H1 Hexy as H1. 
    destruct H1 as [z [w [? [? ?]]]].
    eapply offspring_step_ancestor in H3 as H4; eauto.
    unfold is_bridge in Hb. 
    eapply reachable_without_step_offspring1 in H1 as H7; eauto.
    eapply reachable_without_step_offspring2 in H4 as H8; eauto.
    assert (step_without g exy z w) as H5.
    { unfold step_without. destruct H2 as [e0 [? ?]].
    exists e0; split; auto. }
    (* eapply rt_step in H2 as H5. *)
    eapply sub_reachable_without with (g2:=g) in H7, H8; eauto.
    eapply Hb; eauto.
    eapply no_multiple_edge in He; eauto.
    subst e.
    eapply reachable_without_sym; eauto.
    etransitivity; eauto.
    etransitivity; eauto.
    unfold reachable_without.
    transitivity_1n w; auto.
    reflexivity.
  - intros. 
    pose proof H0 as Hxy.
    destruct H0 as [exy ?].
    pose proof H0 as Hexy.
    apply sub in H0.
    eapply step_sym in H0 as Heyx.
    unfold is_bridge; intros.
    unfold not; intros.
    eapply step_sym in Heyx.
    eapply no_multiple_edge in He; eauto.
    subst exy.
    eapply step_aux_unique_undirected in Heyx; eauto.
    destruct Heyx; destruct H3; subst x0 y0;
    eapply father_unreachable; eauto. 
    eapply reachable_without_sym; eauto.
    Unshelve. auto. auto. auto. auto.
Qed.

Definition reachable_edge (u: V) (e: E): Prop :=
  exists x y, step_aux g e x y /\ reachable g u x.

Lemma tarjan_trivial: forall e, 
  reachable_edge theroot e -> 
  reachable_visited ->
  ~ evalid dfstree e ->
  ~ is_bridge g e.
Proof.
  intros e He Hv H0.
  assert (evalid g e) as H.
  { destruct He as [x [y [He _]]]; 
  eapply step_evalid; eauto. }
  apply no_empty_edge in H as H1.
  destruct H1 as [x [y H1]].
  unfold not in *; intros.
  unfold is_bridge in H2.
  eapply H2; eauto.
  unfold reachable_without.
  transitivity (root dfstree).
  * eapply reachable_without_sym.
  destruct He as [x0 [y0 [He Hr]]].
  assert (vvalid dfstree x). {
  eapply step_aux_unique_undirected in He; eauto.
  destruct He as [He | He]; destruct He; subst x0 y0.
  apply Hv; auto.
  apply Hv; auto.
  unfold reachable in *.
  transitivity_n1 y; auto.
  eapply step_sym'.
  exists e; auto. 
  }
  eapply root_is_root in H3 as H4; eauto.
  unfold reachable in H4.
  clear H1 H2 H3.
  remember (root dfstree) as rt.
  induction_n1 H4.
  ** reflexivity.
  ** transitivity rt0.
  eapply IHrt; eauto.
  unfold reachable_without. 
  transitivity_1n x; try reflexivity.
  destruct H1 as [e0 ?].
  exists e0; split; auto.
  unfold not; intros; subst e0.
  eapply H0; eauto.
  eapply step_evalid; eauto.
  *
  destruct He as [x0 [y0 [He Hr]]].
  assert (vvalid dfstree y). {
  eapply step_aux_unique_undirected in He; eauto.
  destruct He as [He | He]; destruct He; subst x0 y0.
  apply Hv; auto.
  unfold reachable in *.
  transitivity_n1 x; auto.
  exists e; auto.
  apply Hv; auto. 
  }
  eapply root_is_root in H3 as H4.
  unfold reachable in H4.
  clear H1 H2 H3.
  remember (root dfstree) as rt.
  induction_n1 H4.
  ** reflexivity.
  ** transitivity rt0.
  eapply IHrt; eauto.
  transitivity_1n y; try reflexivity.
  destruct H1 as [e0 ?].
  exists e0; split; auto.
  unfold not; intros; subst e0.
  eapply H0; eauto.
  eapply step_evalid; eauto.
  ** auto.
  * simpl; auto.
Qed.

End TARJAN.
