(**
   This file is part of the supplementary material accompanying the
   submission to CPP'20:
   _An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction_
*)
(**
   We build here on the extension of the _paco_ library,
   implementing the _gpaco_ construction and theory described
   in the Section 3: _Generalized Parameterized Coinduction_ of
   the paper, that is provided in the _paco_ folder.
   Using _gpaco_, we formalize in this file the construction
   described in Section 4: _Up-to-tau bisimulation of streams_.
   In particular, it contains the following:
   * Definition of the codata-type of streams and its append operation;
   * Definition of the family of bisimulations [bisim], i.e. in particular
   strong bisimulation and equivalence up-to tau;
   * Definition of the "most general closure of interest", [bisim_trans_clo],
   and proof that it provides a sound reasoning principle to reason up-to
   transitivity of directed [euttge] equations;
   * Proofs that [eq_stream] and [eutt] are equivalence relations;
   * Definition of the closure up-to concat [bisim_concat_clo]
   and proof that it provides a sound reasoning principle to reason
   up-to equivalent up-to-tau prefixes;
   * Proof that (stream,concat) forms a monoid.
 *)

From Paco Require Import paco.
From Coq Require Import
     Nat
     Morphisms
     Program.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(************************** Generic tactics *****************************)

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Tactic Notation "hinduction" hyp(IND) "top"
  := move IND at top; revert_until IND; induction IND.

Ltac inv H := inversion H; clear H; subst.

Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).

Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                                    match H with X => fail 1 | _ => rewrite lem in H end
                    end); repeat rewrite lem).

(************************** Definitions *****************************)

(* We define a coinductive type of streams that may either step silently, or emit a visible [nat] *)
Section Stream.

  (* Functor of the datatype *)
  Variant streamF (stream : Type) :=
  | RetF
  | TauF (s : stream)
  | VisF (e : nat) (s : stream)
  .

  CoInductive stream : Type := go { _observe : streamF stream }.

End Stream.

Notation stream' := (streamF stream).

Definition observe (s : stream) : stream' := @_observe s.

(* These notations alleviate the overhead induced by negative co-inductives *)
Notation Ret := (go RetF).
Notation Tau s := (go (TauF s)).
Notation Vis e s := (go (VisF e s)).

Ltac genobs x ox := remember (observe x) as ox.
Ltac genobs_clear x ox := genobs x ox; match goal with [H: ox = observe x |- _] => clear H x end.
Ltac simpobs := repeat match goal with [H: _ = observe _ |- _] =>
                                       rewrite_everywhere_except (@eq_sym _ _ _ H) H
                       end.

(* Concatenation of streams *)
Section concat.

  Variable k: stream.

  Definition _concat
             (concat : stream -> stream)
             (oc : streamF stream) : stream :=
    match oc with
    | RetF   => k
    | TauF t => Tau (concat t)
    | VisF e h => Vis e (concat h)
    end.

  CoFixpoint concat' (t : stream) : stream :=
    _concat concat' (observe t).

End concat.

Notation concat c k := (concat' k c).
Notation "s1 ;; s2" := (concat s1 s2)
                         (at level 100, right associativity) : stream_scope.

(************************** Shallow equivalence *****************************)

(** ** [observing]: Lift relations through [observe]. *)
Inductive observing
          (eq_ : stream' -> stream' -> Prop)
          (t1 : stream) (t2 : stream) : Prop :=
| observing_intros :
    eq_ t1.(observe) t2.(observe) -> observing eq_ t1 t2.
Hint Constructors observing.

Section observing_relations.

  Variable (eq_ : stream' -> stream' -> Prop).

  Global Instance observing_observe :
    Proper (observing eq_ ==> eq_) (@observe).
  Proof. intros ? ? []; cbv; auto. Qed.

  Global Instance observing_go : Proper (eq_ ==> observing eq_) (@go).
  Proof. repeat intro. cbv; auto. Qed.

  Global Instance monotonic_observing eq_' :
    subrelation eq_ eq_' ->
    subrelation (observing eq_) (observing eq_').
  Proof. intros ? ? ? []; cbv; eauto. Qed.

  Global Instance Equivalence_observing :
    Equivalence eq_ -> Equivalence (observing eq_).
  Proof.
    intros []; split; cbv; auto.
    - intros ? ? []; auto.
    - intros ? ? ? [] []; eauto.
  Qed.

End observing_relations.

(** ** [going]: Lift relations through [go]. *)

Inductive going (r : stream -> stream -> Prop)
          (ot1 : stream') (ot2 : stream') : Prop :=
| going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
Hint Constructors going.

Lemma observing_going (eq_ : stream' -> stream' -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto.
  intros [[]]; auto.
Qed.

Section going_relations.

  Variable (eq_ : stream -> stream -> Prop).

  Global Instance going_go : Proper (going eq_ ==> eq_) (go).
  Proof. intros ? ? []; auto. Qed.

  Global Instance monotonic_going eq_' :
    subrelation eq_ eq_' ->
    subrelation (going eq_) (going eq_').
  Proof. intros ? ? ? []; eauto. Qed.

  Global Instance Equivalence_going :
    Equivalence eq_ -> Equivalence (going eq_).
  Proof.
    intros []; constructor; cbv; eauto.
    - intros ? ? []; auto.
    - intros ? ? ? [] []; eauto.
  Qed.

End going_relations.

(************************** BISIMULATION *****************************)

(** We wish to define two notions of bisimulations over our streams:
    * strong bisimulation, the coinductive pendant to [eq]
    * bisimulation up to tau events, that disregard discrepancies of finite number of internal events.
    Additionally, we want to obtain strong reasoning principles in both cases,
    the later one being challenging. *)

Coercion is_true : bool >-> Sortclass.

Section bisim.

  (** We need to do some gymnastics to work around the
      two-layered definition of [stream]. We first define a
      relation transformer [bisimF] as an indexed inductive type
      on [streamF], which is then composed with [observe] to obtain
      a relation transformer on [stream] ([bisim_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [stream].
   *)

  (**
     (Functorial) definition of bisimulations over streams.
     The definition takes four parameters:
     - [sim] is the currently built coinductive relation
     - [vclo] is the closure of the bisimulation up to which one whishes to reason.
     Its type is hence ((stream -> stream -> Prop) -> stream -> stream -> Prop).
     If we foresee slightly what is to come, the main _definitions_ of the bisimulations will
     takes this closure as the identity.
     But _weaker_ bisimulations, [euttG] in particular, will make good use of this closure
     to soundly recover convenient up-to reasoning principles.
     - [b1] and [b2] are booleans flags.
     Two streams can then be related:
     - by stripping [Tau] on both sides if it simply leads into [sim]
     - by stripping [Vis] on both sides if it leads into the closure of [sim], i.e. [vclo sim]
     - by stripping [Tau] on a single side if it leads to _inductively_ related results _and_ is allowed by the corresponding flag
   *)
  Inductive bisimF (b1 b2: bool) vclo (sim : stream -> stream -> Prop) :
    stream' -> stream' -> Prop :=
  | EqRet:
      bisimF b1 b2 vclo sim RetF RetF
  | EqTau m1 m2
          (REL: sim m1 m2):
      bisimF b1 b2 vclo sim (TauF m1) (TauF m2)
  | EqVis (e : nat) k1 k2
          (REL: vclo sim k1 k2 : Prop):
      bisimF b1 b2 vclo sim (VisF e k1) (VisF e k2)
  | EqTauL s1 os2
           (CHECK: b1)
           (REL: bisimF b1 b2 vclo sim (observe s1) os2):
      bisimF b1 b2 vclo sim (TauF s1) os2
  | EqTauR os1 s2
           (CHECK: b2)
           (REL: bisimF b1 b2 vclo sim os1 (observe s2)):
      bisimF b1 b2 vclo sim os1 (TauF s2)
  .
  Hint Constructors bisimF.

  Definition bisim_ b1 b2 vclo sim : stream -> stream -> Prop :=
    fun s1 s2 => bisimF b1 b2 vclo sim (observe s1) (observe s2).
  Hint Unfold bisim_.

  (** [bisimF] and [bisim_] are both monotone.
      As usual, monotony of the functor is necessary to the [paco] approach.
   *)

  Lemma bisimF_mono b1 b2 x0 x1 vclo vclo' sim sim'
        (IN: bisimF b1 b2 vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    bisimF b1 b2 vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Lemma bisim__mono b1 b2 vclo (MON: monotone2 vclo) : monotone2 (bisim_ b1 b2 vclo).
  Proof. do 2 red. intros. eapply bisimF_mono; eauto. Qed.
  Hint Resolve bisim__mono : paco.

  Lemma bisim_idclo_mono: monotone2 (@id (stream -> stream -> Prop)).
  Proof. unfold id. eauto. Qed.

  Hint Resolve bisim_idclo_mono : paco.

  (* [bisim] is defined using [paco], but taking the identity for closure!
     Later on, we'll come back to this definition using other closures to derive up-to
     reasoning techniques *)
  Definition bisim b1 b2 : stream -> stream -> Prop :=
    paco2 (bisim_ b1 b2 id) bot2.

  (** Strong bisimulation on streams. If [eq_straem s1 s2],
      we say that [s1] and [s2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality.
      We obtain the strong bisimulation by disabling any fantasy in [bisimF]:
      - we already restrained the closure to the identity in [bisim]
      - we now also set both flags to false.
      That is we only allow to relate by stripping either [Tau] or [Vis]
      simultaneously on both sides, and assuming that it always directly falls
      back into the coinductive set.
   *)
  Definition eq_stream := bisim false false.

  (** In contrast, equivalence up-to-tau still does not deal with fancy closure
      (once again, this part is meant for reasoning), but does allow to strip uneven
      number of taus on either sides.
   *)
  Definition eutt := bisim true true.

  (** Finally, [euttge] is an asymmetric relation that allows streams to still get related
      if the left one contains more taus.
      Foreseeing quite a bit the remaining development, the relevance of [euttge] stands in
      that it is always sound to _add_ more taus, but can be unsound to remove some.
   *)
  Definition euttge := bisim true false.

End bisim.

(* begin hide *)
Hint Constructors bisimF.
Hint Unfold bisim_.
Hint Resolve bisim__mono : paco.
Hint Resolve bisim_idclo_mono : paco.
Hint Unfold bisim.
Hint Unfold eq_stream.
Hint Unfold eutt.
Hint Unfold euttge.
Hint Unfold id.
(* end hide *)

Ltac unfold_bisim :=
  (try match goal with [|- bisim_ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: bisim_ _ _ _ _ _ _ |- _ ] => red in H end).

Definition flip_clo {A B C} clo r := @flip A B C (clo (@flip B A C r)).

Lemma bisimF_flip b1 b2 vclo r:
  flip (bisimF b2 b1 (flip_clo vclo) (flip r)) <2= @bisimF b1 b2 vclo r.
Proof.
  intros. induction PR; eauto.
Qed.

Lemma bisim_flip b1 b2:
  forall (u : stream) (v : stream),
    bisim b2 b1 v u -> bisim b1 b2 u v.
Proof.
  pcofix self; pstep. intros u v euv. punfold euv.
  red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
Qed.

Lemma bisim_mon (b1 b2 b1' b2': bool)
      (LEb1: b1 -> b1')
      (LEb2: b2 -> b2'):
  @bisim b1 b2 <2= bisim b1' b2'.
Proof.
  pcofix self. pstep. intros u v euv. punfold euv.
  red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
Qed.

Hint Unfold flip.

Delimit Scope eq_stream_scope with eq_stream.

(** Notations for the three relations.
    You can write [≅] using [[\cong]] in tex-mode *)

Bind Scope stream_scope with stream.
Open Scope stream_scope.

Infix "≅" := (eq_stream) (at level 70) : stream_scope.

Infix "≈" := (eutt) (at level 70) : stream_scope.

Infix "≳" := (euttge) (at level 70) : stream_scope.

(************************** A concrete, most general, closure *****************************)

Section bisim_closure.

  (** *** "Up-to" principles for coinduction. *)

  (**
   By construction, equivalence up-to-tau allows us to strip taus one-at-a-time
   such that we fall back into our coinductive hypothesis.
   In many cases however one may want to be allowed to act at a coarser level.
   This is what up-to principles are for.
   *)

  (**
   One approach to reason up-to is the _companion_ approach¹.

   The key intuition behind up-to reasoning is that in order to prove that some [x]
   is in the greatest fixed-point of a functor [f], it suffices to prove that [x]
   is in a post-fixed point of any functor [g] that admits the same greatest fixed-point.
   In particular, a commonly used class of such functions are of the form [g = clo ∘ f]
   where [clo] is a _compatible_ function for [f], i.e. [clo] such that [clo ∘ f ⊆ f ∘ clo].

   Following this idea, the companion is defined as the least upper bound of all compatible
   functions for [f], hence obtaining a very generic reasoning principle supporting
   four principles:
   1. cmp(b) ⊥ ≡ ν b (soundness)
   2. r + b(cmp b r) ⊆ cmp(b) r (coinduction hypothesis)
   3. x ⊆ cmp(b) r if x ⊆ cmp(b) (r ∪ x) (progress)
   4. clo (cmp b r) ⊆ cmp b r  "for a useful closure" (up-to reasoning)
   Principles 1-3 are the same as the ones provided by paco, the fourth is the
   one of particular interest here.

   Intuitively, the issue with the companion approach is that it is so generic
   that it does not allow for _any_ other reasoning principle to creep into our
   specific case of application.
   For this reason, while we follow the intuitive idea that the construction should
   be built upfront with a general closure, we actually handcraft what is intuitively
   believed to be the "most general closure of practical interest for our domain
   of application". In particular, we shall therefore be able to derive more
   reasoning principles specific to [bisim_trans_clo].

   Specifically, [bisim_trans_clo flags r] relates two streams [s1 s2] assuming
   that we can relate coinductively (i.e. by r) two streams [s1' s2'] such that
   they are bisimilar (w.r.t. the bisimilarity currently considered, i.e. [bisim
   flags]) to respectively [s1 and s2].

   ¹: Coinduction All the Way Up, Damien Pous
   *)

  Inductive bisim_trans_clo b1 b2 b1' b2' (r : stream -> stream -> Prop)
  : stream -> stream -> Prop :=
  | bisim_trans_clo_intro s1 s2 s1' s2'
                         (EQVl: bisim b1 b1' s1 s1')
                         (EQVr: bisim b2 b2' s2 s2')
                         (REL: r s1' s2')
    : bisim_trans_clo b1 b2 b1' b2' r s1 s2
  .
  Hint Constructors bisim_trans_clo.

  (* Now in particular, we are interested in the most general safe instance: it
     is always fair game to do some extra work and trim some more taus: that is if
     [b1'=b2'=false].
     Note that it still gives us four (though only two of
     interest) closures, one for strong bisimulation and one for up-to-tau. *)
  Definition bisimC b1 b2 := bisim_trans_clo b1 b2 false false.
  Hint Unfold bisimC.

  Lemma bisimC_mon b1 b2 r1 r2 s1 s2
        (IN: bisimC b1 b2 r1 s1 s2)
        (LE: r1 <2= r2):
    bisimC b1 b2 r2 s1 s2.
  Proof.
    destruct IN. econstructor; eauto.
  Qed.

  Hint Resolve bisimC_mon : paco.

  (* All closures defined in terms of [bisimC] are weakly compatible with the
     corresponding bisimulation for any reasonable closure for visible events *)
  Lemma bisimC_wcompat b1 b2 vclo
        (MON: monotone2 vclo)
        (CMP: compose (bisimC b1 b2) vclo <3= compose vclo (bisimC b1 b2)):
    wcompatible2 (@bisim_ b1 b2 vclo) (bisimC b1 b2).
  Proof.
    econstructor. pmonauto.
    intros. dependent destruction PR.
    punfold EQVl. punfold EQVr. unfold_bisim.
    hinduction REL before r; intros; clear s1' s2'.
    - remember RetF as x.
      hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
      remember RetF as x.
      hinduction EQVr before r; intros; subst; try inv Heqx; eauto.
    - remember (TauF m1) as x.
      hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
      remember (TauF m3) as y.
      hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
      pclearbot. econstructor. gclo.
      econstructor; cycle -1; eauto with paco.
    - remember (VisF e k1) as x.
      hinduction EQVl before r; intros; subst; try dependent destruction Heqx; try inv CHECK; eauto.
      remember (VisF e0 k3) as y.
      hinduction EQVr before r; intros; subst; try dependent destruction Heqy; try inv CHECK; eauto.
      econstructor. intros. pclearbot.
      eapply MON.
      + apply CMP. econstructor; eauto.
      + intros. apply gpaco2_clo, PR.
    - remember (TauF s1) as x.
      hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
      pclearbot. punfold REL.
    - remember (TauF s2) as y.
      hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
      pclearbot. punfold REL.
  Qed.

  Hint Resolve bisimC_wcompat : paco.

  (* In particular, the identity is one such reasonable closure *)
  Lemma bisim_idclo_compat b1 b2: compose (bisimC b1 b2) id <3= compose id (bisimC b1 b2).
  Proof.
    intros. apply PR.
  Qed.
  Hint Resolve bisim_idclo_compat : paco.

  (* Closures derived from [bisimC] are distributive *)
  Lemma bisimC_dist b1 b2:
    forall r1 r2, bisimC b1 b2 (r1 \2/ r2) <2= (bisimC b1 b2 r1 \2/ bisimC b1 b2 r2).
  Proof.
    intros. destruct PR. destruct REL; eauto.
  Qed.

  Hint Resolve bisimC_dist : paco.

  (* The [guclo] principle is enabled over [bisim_clo_trans] for all [bisimC]
  closures with respect to the corresponding bisimulation for a reasonable
  closure for visible events.
  By [bisim_idclo_compat], the principle is hence in particular available
  with the identity as closure, allowing as first up-to reasoning principle
  to work up-to transitive closure. *)
  Lemma bisim_clo_trans b1 b2 vclo
        (MON: monotone2 vclo)
        (CMP: compose (bisimC b1 b2) vclo <3= compose vclo (bisimC b1 b2)):
    bisim_trans_clo b1 b2 false false <3= gupaco2 (bisim_ b1 b2 vclo) (bisimC b1 b2).
  Proof.
    intros. destruct PR. gclo. econstructor; eauto with paco.
  Qed.

End bisim_closure.

Hint Unfold bisimC.
Hint Resolve bisimC_mon : paco.
Hint Resolve bisimC_wcompat : paco.
Hint Resolve bisim_idclo_compat : paco.
Hint Resolve bisimC_dist : paco.
Arguments bisim_clo_trans : clear implicits.
Hint Constructors bisim_trans_clo.

(** ** Properties of relations *)

(** Instances stating that we have equivalence relations. *)

Section bisim_eq.

  (** *** Properties of relation transformers. *)

  Global Instance Reflexive_bisimF b1 b2 (sim : stream -> stream -> Prop)
  : Reflexive sim -> Reflexive (bisimF b1 b2 id sim).
  Proof.
    red. destruct x; constructor; eauto.
  Qed.

  Global Instance Symmetric_bisimF b (sim : stream -> stream -> Prop)
    : Symmetric sim -> Symmetric (bisimF b b id sim).
  Proof.
    red. induction 2; constructor; subst; eauto.
  Qed.

  Global Instance Reflexive_bisim_ b1 b2 (sim : stream -> stream -> Prop)
    : Reflexive sim -> Reflexive (bisim_ b1 b2 id sim).
  Proof. repeat red. reflexivity. Qed.

  Global Instance Symmetric_bisim_ b (sim : stream -> stream -> Prop)
    : Symmetric sim -> Symmetric (bisim_ b b id sim).
  Proof. repeat red; symmetry; auto. Qed.

  (** *** [bisim] is an equivalence relation *)

  Global Instance Reflexive_bisim_gen b1 b2 (r rg: stream -> stream -> Prop) :
    Reflexive (gpaco2 (bisim_ b1 b2 id) (bisimC b1 b2) r rg).
  Proof.
    gcofix CIH. gstep; intros.
    repeat red. destruct (observe x); eauto with paco.
  Qed.

  Global Instance Reflexive_bisim b1 b2 : Reflexive (bisim b1 b2).
  Proof.
    red; intros. ginit. apply Reflexive_bisim_gen.
  Qed.

  Global Instance Symmetric_bisim b : Symmetric (bisim b b).
  Proof.
    red; intros. apply bisim_flip.
    eapply bisim_mon, H; eauto.
  Qed.

  (** To prove transitivity of [bisim], we rely on transitive up-to reasoning.
      The reasoning principle is enabled by [bisim_clo_trans] via the [guclo]
      tactics that internalizes the administrative details required to apply the
      high level [guclo] reasoning principle.
   *)
  Global Instance Transitive_bisim (b: bool) : Transitive (bisim false b).
  Proof.
    ginit. intros.
    guclo bisim_clo_trans.
    econstructor; [reflexivity|..]; eauto with paco.
    apply bisim_flip. eauto.
  Qed.

  Global Instance Equivalence_bisim : Equivalence (bisim false false).
  Proof.
    constructor; try typeclasses eauto.
  Qed.

  (** *** Congruence properties *)

  Global Instance bisim_observe b1 b2:
    Proper (bisim b1 b2 ==> going (bisim b1 b2)) (observe).
  Proof.
    constructor; punfold H.
  Qed.

  Global Instance bisim_tauF b1 b2:
    Proper (bisim b1 b2 ==> going (bisim b1 b2)) (@TauF _).
  Proof.
    constructor; pstep. econstructor. eauto.
  Qed.

  Global Instance bisim_VisF b1 b2 (e: nat) :
    Proper (bisim b1 b2 ==> going (bisim b1 b2)) (VisF e).
  Proof.
    constructor; red in H. unfold bisim in *. pstep; econstructor; eauto.
  Qed.

  Global Instance observing_sub_bisim l r :
    subrelation (observing eq) (bisim l r).
  Proof.
    repeat red; intros. destruct H.
    pstep. red. rewrite H. apply Reflexive_bisimF. left. apply reflexivity.
  Qed.

  Global Instance eq_sub_bisim:
    subrelation (bisim false false) (bisim true false).
  Proof.
    ginit. gcofix CIH. intros.
    punfold H0. gstep. red in H0 |- *.
    hinduction H0 before CIH; subst; econstructor; try inv CHECK; pclearbot; eauto 7 with paco.
  Qed.

  Global Instance bisim_sub_eutt:
    subrelation (bisim true false) (bisim true true).
  Proof.
    ginit. gcofix CIH. intros.
    punfold H0. gstep. red in H0 |- *.
    hinduction H0 before CIH; subst; econstructor; pclearbot; eauto 7 with paco.
  Qed.

  Global Instance eq_sub_eutt:
    subrelation (bisim false false) (bisim true true).
  Proof.
    red; intros. eapply bisim_sub_eutt. eapply eq_sub_bisim. apply H.
  Qed.

  (** ** Eta-expansion *)

  Lemma stream_eta (t : stream) : t ≅ go (observe t).
  Proof. apply observing_sub_bisim. econstructor. reflexivity. Qed.

  Lemma stream_eta' (ot : stream') : ot = observe (go ot).
  Proof. reflexivity. Qed.

End bisim_eq.

Hint Resolve Reflexive_bisim Reflexive_bisim_gen : reflexivity.

(** *** One-sided inversion *)

Lemma eq_stream_inv_ret (t : stream) :
  t ≅ Ret -> observe t = RetF.
Proof.
  intros; punfold H; inv H; try inv CHECK; eauto.
Qed.

Lemma eq_stream_inv_vis (t : stream) (e : nat) k :
  t ≅ Vis e k -> exists k', observe t = VisF e k' /\ k' ≅ k.
Proof.
  intros; punfold H; red in H; dependent destruction H; try inv CHECK.
  eexists; split; eauto.
  intros. destruct REL; try contradiction; pclearbot; eauto.
Qed.

Lemma eq_stream_inv_tau (t t' : stream) :
  t ≅ Tau t' -> exists t0, observe t = TauF t0 /\ t0 ≅ t'.
Proof.
  intros; punfold H; inv H; try inv CHECK; pclearbot; eauto.
Qed.

Lemma bisim_inv_vis b1 b2 (e1 e2: nat) (k1 k2: stream) :
  bisim b1 b2 (Vis e1 k1) (Vis e2 k2) -> e1 = e2 /\ bisim b1 b2 k1 k2.
Proof.
  intros. punfold H. repeat red in H. simpl in H.
  dependent destruction H. pclearbot. eauto.
Qed.

Lemma bisim_inv_tauL b1 s1 s2 :
  bisim b1 true (Tau s1) s2 -> bisim b1 true s1 s2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF s1) as ts1. genobs s2 os2.
  hinduction H before b1; intros; try discriminate.
  - inv Heqts1. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqts1. punfold_reverse H.
  - red in IHbisimF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma bisim_inv_tauR b2 s1 s2 :
  bisim true b2 s1 (Tau s2) -> bisim true b2 s1 s2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF s2) as ts2. genobs s1 os1.
  hinduction H before b2; intros; try discriminate.
  - inv Heqts2. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - red in IHbisimF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
  - inv Heqts2. punfold_reverse H.
Qed.

Lemma bisim_tauL b2 (s1 : stream) (s2 : stream) :
  bisim true b2 s1 s2 -> bisim true b2 (Tau s1) s2.
Proof.
  intros. pstep. econstructor; eauto. punfold H.
Qed.

Lemma bisim_tauR b1 (s1 : stream) (s2 : stream) :
  bisim b1 true s1 s2 -> bisim b1 true s1 (Tau s2).
Proof.
  intros. pstep. econstructor; eauto. punfold H.
Qed.

Lemma tau_eutt (t: stream) :
  Tau t ≳ t.
Proof.
  apply bisim_tauL. reflexivity.
Qed.

Lemma simpobs {ot} {t: stream} (EQ: ot = observe t): t ≅ go ot.
Proof.
  pstep. repeat red. simpobs. simpl. subst. pstep_reverse. apply Reflexive_bisim.
Qed.

(** *** Transitivity properties *)

(* Reasoning up-to [bisim_trans_clo] in this proof *)
Lemma bisim_trans b (s1 s2 t3: stream)
      (REL1: bisim b false s1 s2)
      (REL2: bisim b false s2 t3):
  bisim b false s1 t3.
Proof.
  ginit. guclo bisim_clo_trans; eauto.
  econstructor; eauto with paco. reflexivity.
Qed.

(* In contrast, reasoning up-to [bisim_trans_clo] is of no help
   when proving the transitivity of [eutt]: the closure only allows
   for (directed) rewriting by [euttge] via [bisimC], but not general
   [eutt] equations.
   We hence proceed "by hand": by coinduction, followed by nested
   induction over the two functors [bisimF].
 *)
Lemma eutt_trans (s1 s2 t3: stream)
      (INL: s1 ≈ s2)
      (INR: s2 ≈ t3):
  s1 ≈ t3.
Proof.
  reverse.
  pcofix CIH. intros.
  pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear s1 s2; eauto.
  - remember RetF as ot.
    hinduction INR before CIH; intros; inv Heqot; eauto with paco.
  - assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      eapply bisim_inv_tauL. eapply bisim_inv_tauR. eauto.
    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      pclearbot. punfold REL. red in REL.
      hinduction REL0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * subst. eapply bisimF_mono; eauto. intros.
        eapply upaco2_mon; eauto; contradiction.
      * remember (VisF e k1) as ot.
        hinduction REL0 before CIH; intros; dependent destruction Heqot; eauto with paco.
        econstructor. intros. right.
        destruct REL, REL0; try contradiction. eauto.
      * eapply IHREL0; eauto. pstep_reverse.
        apply bisim_inv_tauR. eauto.
  - remember (VisF e k2) as ot.
    hinduction INR before CIH; intros; dependent destruction Heqot; eauto.
    econstructor. intros.
    destruct REL, REL0; try contradiction; eauto.
  - remember (TauF s0) as ot.
    hinduction INR before CIH; intros; dependent destruction Heqot; eauto.
    eapply IHINL. pclearbot. punfold REL.
Qed.

Global Instance Transitive_eutt : Transitive eutt.
Proof.
  red; intros. eapply eutt_trans; eauto.
Qed.

Global Instance Equivalence_eutt : Equivalence eutt.
Proof.
  constructor; try typeclasses eauto.
Qed.

Global Instance geuttgen_cong_bisim b1 b2 r rg:
  Proper (eq_stream ==> eq_stream ==> flip impl)
         (gpaco2 (bisim_ b1 b2 id) (bisimC b1 b2) r rg).
Proof.
  repeat intro. guclo bisim_clo_trans. econstructor; cycle -1; eauto.
  - eapply bisim_mon, H; eauto; discriminate.
  - eapply bisim_mon, H0; eauto; discriminate.
Qed.

Global Instance geuttge_cong_euttge r rg:
  Proper (euttge ==> eq_stream ==> flip impl)
         (gpaco2 (bisim_ true false id) (bisimC true false) r rg).
Proof.
  repeat intro. guclo bisim_clo_trans.
Qed.

Global Instance geutt_cong_euttge r rg:
  Proper (euttge ==> euttge ==> flip impl)
         (gpaco2 (bisim_ true true id) (bisimC true true) r rg).
Proof.
  repeat intro. guclo bisim_clo_trans.
Qed.

Global Instance bisimgen_cong_bisim b1 b2:
  Proper (eq_stream ==> eq_stream ==> flip impl)
         (bisim b1 b2).
Proof.
  ginit. intros. rewrite H1, H0. gfinal. eauto.
Qed.

Global Instance euttge_cong_euttge:
  Proper (euttge ==> flip euttge ==> flip impl)
         (bisim true false).
Proof.
  repeat intro. do 2 eapply bisim_trans; eauto. reflexivity.
Qed.

(** ** Equations for core combinators *)
Lemma unfold_concat_
      (t : stream) (k : stream):
  observing eq
            (concat t k)
            (_concat k (fun t => concat t k) (observe t)).
Proof. eauto. Qed.

Lemma unfold_concat
      (t : stream) (k : stream) :
  concat t k ≅ _concat k (fun t => concat t k) (observe t).
Proof. rewrite unfold_concat_. reflexivity. Qed.

Lemma concat_ret_ (k : stream) :
  observing eq (concat Ret k) k.
Proof. apply unfold_concat_. Qed.

Lemma concat_ret (k : stream) :
  concat Ret k ≅ k.
Proof. rewrite concat_ret_. reflexivity. Qed.

Lemma concat_tau_ t (k: stream):
  observing eq (concat (Tau t) k) (Tau (concat t k)).
Proof. apply @unfold_concat_. Qed.

Lemma concat_tau t (k: stream) :
  concat (Tau t) k ≅ Tau (concat t k).
Proof. rewrite concat_tau_. reflexivity. Qed.

Lemma concat_vis_ (e: nat) (ek: stream) (k: stream) :
  observing eq
            (concat (Vis e ek) k)
            (Vis e (concat ek k)).
Proof. apply @unfold_concat_. Qed.

Lemma concat_vis (e: nat) (ek: stream) (k: stream) :
  concat (Vis e ek) k ≅ Vis e (concat ek k).
Proof. rewrite concat_vis_. reflexivity. Qed.

Section bisim_h.

  (** [bisim] is a congruence for [stream] constructors. *)

  Lemma bisim_Tau b1 b2 (s1 : stream) (s2 : stream) :
    bisim b1 b2 (Tau s1) (Tau s2) <-> bisim b1 b2 s1 s2.
  Proof.
    split; intros H.
    - punfold H. red in H. simpl in *. pstep. red.
      remember (TauF s1) as os1. remember (TauF s2) as os2.
      hinduction H before b2; intros; subst; try inv Heqos1; try inv Heqos2; eauto.
      + pclearbot. punfold REL.
      + inv H; eauto.
      + inv H; eauto.
    - pstep. constructor; auto.
  Qed.

  Lemma bisim_Vis b1 b2 (e : nat)
        (k1 : stream) (k2 : stream) :
    (bisim b1 b2 k1 k2)
    <-> bisim b1 b2 (Vis e k1) (Vis e k2).
  Proof.
    split; intros H.
    - pstep. econstructor. left. apply H.
    - punfold H. red in H; dependent destruction H; auto.
      intros. pclearbot. eauto.
  Qed.

  (** *** "Up-to" [concat] principle for coinduction. *)

  (* [bisim_clo_trans] has given us reasoning up-to transitivity by [euttge].
     A second crucial reasoning principle is to be able to reason up-to [concat]:
     when coinductively relating by a bisimulation [b] two streams defined as concats,
     the prefixes can be stripped of assuming they are related by [b].
   *)
  Inductive bisim_concat_clo b1 b2 (r : stream -> stream -> Prop) :
    stream -> stream -> Prop :=
  | pbc_intro_h s1 s2 k1 k2
                (EQV: bisim b1 b2 s1 s2)
                (REL: r k1 k2)
    : bisim_concat_clo b1 b2 r (concat s1 k1) (concat s2 k2) .
  Hint Constructors bisim_concat_clo.

  (* The [guclo] principle over [bisim_concat_clo] is enabled for all [bisimC]
     closures with respect to the corresponding bisimulation for a reasonable
     closure for visible events, hence the identity in particular.
     Note the use of a reasoning up-to [bisim_clo_trans] to prove this.
   *)
  Lemma bisim_clo_concat b1 b2 vclo
        (MON: monotone2 vclo)
        (CMP: compose (bisimC b1 b2) vclo <3= compose vclo (bisimC b1 b2))
        (ID: id <3= vclo):
    bisim_concat_clo b1 b2 <3= gupaco2 (bisim_ b1 b2 vclo) (bisimC b1 b2).
  Proof.
    gcofix CIH. intros. destruct PR.
    guclo bisim_clo_trans.
    econstructor; try (rewrite unfold_concat; reflexivity).
    punfold EQV. unfold_bisim.
    hinduction EQV before CIH; intros; pclearbot.
    - guclo bisim_clo_trans.
      econstructor; try reflexivity.
      eauto with paco.
    - gstep. econstructor. eauto with paco.
    - gstep. econstructor. eauto 7 with paco.
    - destruct b1; try discriminate.
      guclo bisim_clo_trans. econstructor; cycle -1; eauto; try reflexivity.
      eapply bisim_tauL. rewrite unfold_concat; reflexivity.
    - destruct b2; try discriminate.
      guclo bisim_clo_trans. econstructor; cycle -1; eauto; try reflexivity.
      eapply bisim_tauL. rewrite unfold_concat. reflexivity.
  Qed.

  Lemma eutt_clo_concat s1 s2 k1 k2
        (EQT: eutt s1 s2)
        (EQK: eutt k1 k2):
    eutt (s1;; k1) (s2;; k2).
  Proof.
    intros. ginit. guclo bisim_clo_concat.
  Qed.

End bisim_h.

Arguments bisim_clo_concat : clear implicits.
Hint Constructors bisim_concat_clo.

(* Straightforward use of reasoning up-to [bisim_clo_concat] *)
Lemma bisim_concat' b1 b2 s1 s2 k1 k2 :
  bisim b1 b2 s1 s2 ->
  bisim b1 b2 k1 k2 ->
  bisim b1 b2 (s1;;k1) (s2;;k2).
Proof.
  intros. ginit. guclo bisim_clo_concat.
Qed.

Global Instance bisim_concat b1 b2 :
  Proper (bisim b1 b2 ==>
               bisim b1 b2 ==>
               bisim b1 b2) (concat').
Proof.
  repeat intro; eapply bisim_concat'; eauto.
Qed.

Global Instance bisim_concat_ b1 b2 k :
  Proper (going (bisim b1 b2) ==>
                bisim b1 b2) (_concat k (concat' k)).
Proof.
  ginit. intros. destruct H0.
  rewrite (@stream_eta' x), (@stream_eta' y), <- !unfold_concat.
  guclo bisim_clo_concat. econstructor; eauto.
  intros. subst. apply reflexivity.
Qed.

Lemma concat_res2 :
  forall s : stream,
    concat s Ret ≅ s.
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_concat. gstep. repeat red.
  genobs s os. destruct os; simpl; eauto with paco.
Qed.

Lemma concat_concat :
  forall (s : stream) (k : stream) (h : stream),
    concat (concat s k) h ≅ concat s (concat k h).
Proof.
  ginit. gcofix CIH. intros. rewrite !unfold_concat.
  gstep. repeat red. destruct (observe s); simpl; eauto with paco.
  apply reflexivity.
Qed.

Hint Rewrite @concat_ret : stream.
Hint Rewrite @concat_tau : stream.
Hint Rewrite @concat_vis : stream.
Hint Rewrite @concat_res2 : stream.
Hint Rewrite @concat_concat : stream.
