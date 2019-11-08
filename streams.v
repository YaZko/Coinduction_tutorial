Require Import Paco.paco.
From Coq Require Import
     Morphisms.

Set Implicit Arguments.
Set Primitive Projections.

Module streams.

  Variant streamF {A} (stream : Type) : Type :=
  | ConsF (a : A) (s : stream) : streamF stream
  .

  CoInductive stream A : Type :=
    go { _observe : @streamF A (stream A) }.

  Notation Cons a s := (go (ConsF a s)).

  CoFixpoint ones : stream nat := Cons 1 ones.
  CoFixpoint twos : stream nat := Cons 2 twos.
  Goal ~ ones = twos.
    Fail destruct ones. (* Primitive Projection disallows this *)
    destruct (_observe ones) eqn:?.
  Abort.

  Variant eq_streamF A eq_stream : @streamF A (stream A) -> @streamF A (stream A) -> Prop :=
  | eq_ConsF a s s' : eq_stream s s' -> eq_streamF eq_stream (ConsF a s) (ConsF a s').

  CoInductive eq_stream {A} (s s' : stream A) : Prop :=
    { _observe' : @eq_streamF A eq_stream (_observe s) (_observe s') }.

  Goal ~ eq_stream ones twos.
    intro. inversion H. cbn in *. inversion _observe'0.
  Qed.

  Fixpoint approx {A} n (s : stream A) : list A :=
    match n with
    | O => nil
    | S n => match (_observe s) with
            | ConsF a s => cons a (approx n s)
            end
    end.

  Compute approx 10 ones.

  CoFixpoint map {A B} (f : A -> B) (s : stream A) : stream B :=
    match (_observe s) with
    | ConsF a s => Cons (f a) (map f s)
    end.

  Compute approx 10 (map (fun x => x + 1) ones).

  Lemma eq_stream_map A B (f : A -> B) : forall s1 s2, eq_stream s1 s2 -> eq_stream (map f s1) (map f s2).
  Proof.
    cofix CIH. intros. destruct H. constructor. cbn. inversion _observe'0; subst.
    destruct (_observe s1), (_observe s2).
    constructor. apply CIH. auto.
  Qed.

  Definition twos' := map (fun x => x + 1) ones.

  Lemma twos_twos' : eq_stream twos twos'.
  Proof.
    cofix CIH.
    constructor. cbn. constructor. apply CIH.
  Qed.

  (* maybe delete these instances, I don't think I'll use them *)
  Instance Reflexive_eq_stream A : Reflexive (@eq_stream A).
  Proof.
    red. cofix CIH. constructor. destruct (_observe x).
    constructor. apply CIH.
  Qed.

  Instance Symmetric_eq_stream A : Symmetric (@eq_stream A).
  Proof.
    red. cofix CIH.
    constructor. destruct H.
    destruct (_observe x), (_observe y). inversion _observe'0; subst.
    constructor. apply CIH. auto.
  Qed.

  Instance Transitive_eq_stream A : Transitive (@eq_stream A).
  Proof.
    red. cofix CIH. repeat intro.
    constructor. destruct H. destruct H0.
    destruct (_observe x), (_observe y), (_observe z).
    inversion _observe'0; subst. inversion _observe'1; subst.
    constructor. eapply CIH; eauto.
  Qed.

  Lemma trans_eq_stream A : forall (s1 s2 s3 : stream A),
      eq_stream s1 s2 ->
      eq_stream s2 s3 ->
      eq_stream s1 s3.
  Proof.
    cofix CIH. repeat intro.
    constructor. destruct H. destruct H0.
    destruct (_observe s1), (_observe s2), (_observe s3).
    inversion _observe'0; subst. inversion _observe'1; subst.
    constructor. eapply CIH; eauto.
  Qed.

  Lemma eq_stream_map' A B (f : A -> B) : forall s1 s2 s3,
      eq_stream s1 s2 ->
      eq_stream s2 s3 ->
      eq_stream (map f s1) (map f s3).
  Proof.
    cofix CIH. intros. destruct H, H0. constructor. cbn.
    inversion _observe'0; subst.
    inversion _observe'1; subst. rewrite <- H2 in H0. inversion H0; subst.
    destruct (_observe s1), (_observe s2), (_observe s3).
    constructor. eapply CIH; eauto.
  Qed.
End streams.

Module trees.
  Variant treeF {A} (tree : Type) : Type :=
  | NodeF (a : A) (l r : tree) : treeF tree
  .

  CoInductive tree A : Type :=
    go { _observe : @treeF A (tree A) }.

  Notation Node a l r := (go (NodeF a l r)).

  Variant eq_treeF A eq_tree : @treeF A (tree A) -> @treeF A (tree A) -> Prop :=
  | eq_NodeF a l l' r r' : eq_tree l l' ->
                           eq_tree r r' ->
                           eq_treeF eq_tree (NodeF a l r) (NodeF a l' r').

  CoInductive eq_tree {A} (t t' : tree A) : Prop :=
    { _observe' : @eq_treeF A eq_tree (_observe t) (_observe t') }.

  CoFixpoint ones : tree nat := Node 1 ones twos
  with twos : tree nat := Node 2 ones twos.

  CoFixpoint ones' : tree nat := Node 1 ones' twos'
  with twos' : tree nat := Node 2 ones' twos'.

  Lemma ones_ones' : eq_tree ones ones'.
  Proof.
    cofix CIH.
    constructor. cbn. constructor; auto.
    cofix CIH'.
    constructor. cbn. constructor; auto.
  Qed.

  (* This proof has the exact same structure *)
  Lemma twos_twos' : eq_tree twos twos'.
  Proof.
    cofix CIH.
    constructor. cbn. constructor; auto.
    cofix CIH'.
    constructor. cbn. constructor; auto.
  Qed.

  (* We can try splitting out the common parts of the two above proofs *)

  Lemma twos_ones : eq_tree twos twos' -> eq_tree ones ones'.
  Proof.
    intros. cofix CIH.
    constructor. cbn. constructor; auto.
  Defined.
  Lemma ones_twos : eq_tree ones ones' -> eq_tree twos twos'.
  Proof.
    intros. cofix CIH.
    constructor. cbn. constructor; auto.
  Defined.

  (* Note that we cannot use this lemma in the proof below, since the
     _proof_ does not guard the CIH in ones_ones''. *)
  Lemma twos_ones_different_proof : eq_tree twos twos' -> eq_tree ones ones'.
  Proof.
    intros.
    inversion H. cbn in *. inversion _observe'0. auto.
  Defined.

  (* However to use these lemmas, they need to be made transparent
  (using Defined) so syntactic guardedness checking succeeds. *)
  Lemma ones_ones'' : eq_tree ones ones.
  Proof.
    cofix CIH.
    apply twos_ones. apply ones_twos. apply CIH.
  Qed.

  Definition eq_tree_ A eq_tree : tree A -> tree A -> Prop :=
    fun t t' => eq_treeF eq_tree (_observe t) (_observe t').
  Definition eq_tree' {A} : tree A -> tree A -> Prop := paco2 (@eq_tree_ A) bot2.

  (* Lemma eq_treeF_mono A : monotone2 (eq_treeF A). *)
  Lemma eq_tree__mon A : monotone2 (@eq_tree_ A).
  Proof.
    repeat intro. unfold eq_tree_ in *. destruct (_observe x0), (_observe x1).
    inversion IN; subst. constructor; auto.
  Qed.
  Hint Resolve eq_tree__mon : paco.
  Hint Unfold eq_tree_.

  Lemma ones_ones''' : eq_tree' ones ones'.
  Proof.
    pcofix CIH.
    pfold. red. cbn. constructor.
    - right. auto.
    - left. pcofix CIH'. pfold. red. cbn. constructor; right; auto.
  Qed.

  Lemma twos_ones' : forall r, (r twos twos' : Prop) -> paco2 (@eq_tree_ nat) r ones ones'.
  Proof.
    intros. pcofix CIH. pfold. red. cbn. constructor; right; auto.
  Qed.
  Lemma ones_twos' : forall r, (r ones ones' : Prop) -> paco2 (@eq_tree_ nat) r twos twos'.
  Proof.
    intros. pcofix CIH. pfold. red. cbn. constructor; right; auto.
  Qed.

  Lemma ones_ones'''' : eq_tree' ones ones.
  Proof.
    pcofix CIH.
    pmult. apply twos_ones'. apply ones_twos'. auto.
  Qed.

End trees.
