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