(**
   This file is part of the supplementary material accompanying the
   submission to CPP'20:
   _An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction_
*)
(**
   Using the new proposed _gpaco_ construction, _stream.v_ built
   over a codata-type of streams notably a bisimulation up-to-taus
   and equipped it with up-to reasoning principles for directed
   transitive closure and concatenation of up-to-tau prefixes.
   In this file, we internalize all low level details to
   define a new bisimulation predicate [euttG] providing a
   clean, high-level, axiomatic interface allowing for sound
   reasoning while aiming to establish that two streams are [eutt].
   In particular, this file contains the following:
   * Definition of [euttG], a bisimulation parameterized by
   four predicates;
   * Proof of its soundness with respect to [eutt]
   * Proof of three up-to reasoning principles: we recover
   reasoning up-to directed transitive closure and up-to
   concatenation of [eutt] prefixes at a higher level, but
   we additionally get a constrained reasoning up-to undirected
   transitive closure.
   * We encapsulate the interface into high-level tactics.
*)

(* begin hide *)
From Paco Require Import paco.
From Coq Require Import
     Nat
     Morphisms
     Program.

From EuttG Require Import stream.
(* end hide *)

(************************** EUTT *****************************)
Section EUTTG.

  (* Undirected transitive closure: streams are considered up to tau equivalence
     without discrimination, in contrast with [bisimC] from _stream.v_.
     Note once again that this principle _cannot_ be always sound since it
     could allow one to put back in place a tau step seemingly used as a guard *)

  Definition transU := bisim_trans_clo true true true true.

  (** The following example illustrates why this reasoning principle
      _cannot_ be sound in general:

  (* Assuming that [transU] could be used up-to with no constraints *)
  Axiom bisim_clo_trans_gen:
         forall b1 b2 vclo
           (MON: monotone2 vclo)
           (CMP: compose transU vclo <3= compose vclo transU),
           transU <3= gupaco2 (bisim_ b1 b2 vclo) (bisimC true true).
  (* Then we could prove the following absurd statement: *)
  Goal Vis 1 Ret ≈ Vis 2 Ret.
    (* Indeed, we proceed by coinduction *)
    ginit. gcofix CIH.
    (* Clearly, _adding_ a Tau in front of each stream preserves [eutt] *)
    assert (eq1: Vis 1 Ret ≈ Tau (Vis 1 Ret)) by (ginit; gstep; constructor; auto with paco; reflexivity).
    assert (eq2: Vis 2 Ret ≈ Tau (Vis 2 Ret)) by (ginit; gstep; constructor; auto with paco; reflexivity).
    (* And that's exactly what this general transitive closure allow us to do *)
    guclo bisim_clo_trans_gen. econstructor; eauto.
    (* But then these exact two new Taus can be used as guards to step *)
    gstep; constructor.
    (* Allowing us to conclude by using our coinduction hypothesis *)
    gbase; assumption.
  Qed.
   *)

  (* Directed transitive closure: streams are considered up to _removal_ of taus.
     This principle should be sound in all contexts.
     Not that this is a synonymous of [bisimC] from the file _stream.v_ for uniformity
     of notations.
   *)
  Definition transD := bisim_trans_clo true true false false.

  (* Closure up to concat: if both streams are defined as concats, and their prefix
     are eutt, these prefixes may be shaved off *)
  Definition concatC :=  bisim_concat_clo true true.

(* Intuition: four predicates that indicate information accessible under or above each guard.
   The parameters should be read as regular/guarded low/high.
   All information is closed by directed transitivity, as adding taus is always sound.
   Any knowledge guarded by visible guards is closed under undirected transitivity,
   as removing taus cannot undo a visible guard.
   The lowly guarded knowledge is always unlocked after a step.
   Access to the high guarded knowledge is conditioned to having taken a visible step.
   This is enforced by hiding the knowledge inside of the closure provided to [bisim_].
 *)
  Definition euttVC gH r :=
    gupaco2 (bisim_ true true id) transD (transU (r \2/ gH)).

  Variant euttG rH rL gL gH t1 t2 : Prop :=
  | euttG_intro
      (IN: gpaco2 (@bisim_ true true (euttVC gH)) transD (transU rH \2/ rL) gL t1 t2).

  Hint Unfold transU transD concatC euttVC.
  Hint Constructors euttG.

  Lemma transD_mon r1 r2 t1 t2
        (IN: transD r1 t1 t2)
        (LE: r1 <2= r2):
    transD r2 t1 t2.
  Proof. eapply bisimC_mon, LE; eauto. Qed.

  Lemma transU_mon r1 r2 t1 t2
        (IN: transU r1 t1 t2)
        (LE: r1 <2= r2):
    transU r2 t1 t2.
  Proof.
    destruct IN. econstructor; eauto.
  Qed.

  Lemma transDleU: transD <3= transU.
  Proof.
    intros. destruct PR. econstructor; eauto using bisim_mon.
  Qed.

  Lemma transD_compose:
    compose transD transD <3= transD.
  Proof.
    intros. destruct PR. destruct REL.
    econstructor; cycle -1; eauto; eapply bisim_trans; eauto using bisim_mon.
  Qed.

  Lemma transU_compose:
    compose transU transU <3= transU.
  Proof.
    intros. destruct PR. destruct REL.
    econstructor; cycle -1; eauto; eapply eutt_trans; eauto using bisim_mon.
  Qed.

  Lemma transD_id: id <3= transD.
  Proof. intros. econstructor; eauto; reflexivity. Qed.

  Lemma transU_id: id <3= transU.
  Proof. intros. econstructor; eauto; reflexivity. Qed.

  Hint Resolve transD_mon transU_mon : paco.

  Lemma euttVC_mon gH:
    monotone2 (euttVC gH).
  Proof.
    red; intros.
    eapply gupaco2_mon; eauto. intros.
    eapply transU_mon; eauto. intros.
    destruct PR0; eauto.
  Qed.
  Hint Resolve euttVC_mon : paco.

  Lemma euttVC_compat gH:
    compose transD (euttVC gH) <3= compose (euttVC gH) transD.
  Proof.
    intros. gclo.
    eapply transD_mon; eauto. intros.
    eapply gupaco2_mon; eauto; intros.
    eapply transU_mon; eauto. intros.
    destruct PR2; eauto.
    left. econstructor; eauto; reflexivity.
  Qed.
  Hint Resolve euttVC_compat : paco.

  Lemma euttVC_id gH:
    id <3= euttVC gH.
  Proof.
    intros. gbase. econstructor; eauto; reflexivity.
  Qed.
  Hint Resolve euttVC_id : paco.

End EUTTG.

Hint Unfold transU transD concatC euttVC.
Hint Constructors euttG.
Hint Resolve transD_mon transU_mon : paco.
Hint Resolve euttVC_mon : paco.
Hint Resolve euttVC_compat : paco.
Hint Resolve transD_id transU_id euttVC_id : paco.

Instance geuttG_cong_euttge gH r g:
  Proper (euttge ==> euttge ==> flip impl)
         (gpaco2 (bisim_ true true (euttVC gH)) transD r g).
Proof.
  repeat intro. guclo bisim_clo_trans.
Qed.

Instance geuttG_cong_eq gH r g:
  Proper (eq_stream ==> eq_stream ==> flip impl)
         (gpaco2 (bisim_ true true (euttVC gH)) transD r g).
Proof.
  repeat intro. eapply geuttG_cong_euttge; eauto using bisim_mon.
Qed.

(* Auxiliary lemmas *)
Section EUTTG_Properties1.

  Lemma rclo_transD r:
    rclo2 transD r <2= transD r.
  Proof.
    intros. induction PR.
    - econstructor; eauto; reflexivity.
    - destruct IN. apply H in REL. destruct REL.
      econstructor; cycle -1; eauto using bisim_trans.
  Qed.

  Lemma rclo_flip clo (r: stream -> stream -> Prop)
        (MON: monotone2 clo):
    flip (rclo2 (fun x : stream -> stream -> Prop => flip (clo (flip x))) (flip r)) <2= rclo2 clo r.
  Proof.
    intros. induction PR; eauto with paco.
    apply rclo2_clo; eauto.
  Qed.

  Lemma transD_flip r:
    flip (transD (flip r)) <2= transD r.
  Proof.
    intros. destruct PR. econstructor; cycle -1; eauto.
  Qed.

  Lemma transU_flip r:
    flip (transU (flip r)) <2= transU r.
  Proof.
    intros. destruct PR. econstructor; cycle -1; eauto.
  Qed.

  Lemma euttVC_flip gH r:
    flip (euttVC (flip gH) (flip r)) <2= euttVC gH r.
  Proof.
    gcofix CIH. intros. gunfold PR.
    gclo. apply rclo_transD.

    eapply rclo_flip; eauto with paco.
    eapply rclo2_mon_gen; eauto; intros.
    { destruct PR0; eauto using transU_flip. }
    destruct PR0; cycle 1.
    { gbase. destruct H; eauto using transU_flip. }
    gstep. apply bisimF_flip.
    eapply bisimF_mono; eauto with paco. intros.
    gbase. eapply CIH.
    eapply gupaco2_mon; eauto. intros.
    destruct PR1; eauto.
  Qed.

  Lemma euttG_flip gH r:
    flip (gupaco2 (bisim_ true true (euttVC (flip gH))) transD (flip r)) <2=
    gupaco2 (bisim_ true true (euttVC gH)) transD r.
  Proof.
    gcofix CIH; intros.
    destruct PR. econstructor.
    eapply rclo_flip; eauto with paco.
    eapply rclo2_mon_gen; eauto using transD_flip. intros.
    destruct PR; eauto.
    left. punfold H. pstep. apply bisimF_flip.
    eapply bisimF_mono; eauto with paco; intros.
    - eapply euttVC_flip. apply PR.
    - apply rclo_flip; eauto with paco.
      eapply rclo2_mon_gen; eauto using transD_flip with paco.
      intros. right. left. destruct PR0.
      + eapply CIH. red. eauto with paco.
      + apply CIH0. destruct H0; eauto.
  Qed.

  Lemma bisim_ret_gen t1
        (IN: bisim true true t1 Ret):
    bisim true false t1 Ret.
  Proof.
    punfold IN. pstep. red in IN |- *. simpl in *.
    remember RetF as ot.
    hinduction IN top; intros; subst; eauto; inv Heqot.
  Qed.

  Lemma transD_dist:
    forall r1 r2, @transD (r1 \2/ r2) <2= (transD r1 \2/ transD r2).
  Proof. apply bisimC_dist. Qed.

  Lemma transU_dist:
    forall r1 r2, @transU (r1 \2/ r2) <2= (transU r1 \2/ transU r2).
  Proof.
    intros. destruct PR. destruct REL; eauto.
  Qed.

  Lemma transU_dist_rev:
    forall r1 r2, (transU r1 \2/ transU r2) <2= @transU (r1 \2/ r2).
  Proof.
    intros. destruct PR, H; eauto.
  Qed.

  Variant transL (r: stream -> stream -> Prop) t1 t2 : Prop :=
  | transL_intro t' (EQL: t1 ≈ t') (EQR: r t' t2): transL r t1 t2
  .
  Hint Constructors transL.

  Lemma transD_transL r:
    transD (transL r) <2= transL (transD r).
  Proof.
    intros. destruct PR, REL.
    econstructor; [|econstructor]; cycle -1; eauto.
    - rewrite EQVl, EQL. reflexivity.
    - reflexivity.
  Qed.

  Lemma transLleU: transL <3= transU.
  Proof.
    intros. destruct PR. econstructor; eauto. reflexivity.
  Qed.

  Lemma transL_closed vclo r
        (MON: monotone2 vclo)
        (COMP: wcompatible2 (bisim_ true true vclo) transD)
        (CLOV: forall r (CLOL: transL r <2= r), transL (vclo r) <2= vclo r)
        (CLOL: transL r <2= r)
        (CLOD: transD r <2= r):
    transL (gupaco2 (bisim_ true true vclo) transD r)
    <2= gupaco2 (bisim_ true true vclo) transD r.
  Proof.
    gcofix CIH. intros t1 t2 [].
    apply gpaco2_dist in EQR; eauto with paco.
    destruct EQR; cycle 1.
    { gbase. apply rclo_transD in H. destruct H. eauto 7. }
    assert (REL: paco2 (bisim_ true true vclo) r t' t2).
    { eapply paco2_mon; eauto. intros.
      apply rclo_transD in PR. apply CLOD.
      eapply transD_mon; eauto. intros. destruct PR0; eauto.
    }
    clear H.

    punfold EQL. red in EQL. punfold REL. red in REL. genobs t1 ot1. genobs t' ot'.
    hinduction EQL before CIH; intros; subst.
    - remember RetF as ot. genobs t2 ot2.
      hinduction REL before CIH; intros; subst; try inv Heqot.
      + gstep. red. simpobs. eauto.
      + gclo. econstructor; cycle -1; eauto.
        * rewrite (simpobs Heqot1). reflexivity.
        * rewrite (simpobs Heqot2), tau_eutt. reflexivity.
    - pclearbot. apply bisim_tauR in REL. rewrite Heqot' in REL, REL0. clear m2 Heqot'.
      genobs t' ot'. genobs t2 ot2.
      hinduction REL0 before CIH; intros; subst.
      + apply bisim_ret_gen in REL.
        gclo. econstructor.
        * rewrite (simpobs Heqot1), tau_eutt, REL. reflexivity.
        * rewrite (simpobs Heqot2). reflexivity.
        * gstep. econstructor.
      + gstep. red. simpobs. econstructor. gbase.
        destruct REL.
        * eapply CIH; econstructor; cycle -1; eauto using paco2_mon with paco.
          rewrite REL0, tau_eutt. reflexivity.
        * eapply CIH0. apply CLOL. econstructor; cycle 1; eauto.
          rewrite REL0, tau_eutt. reflexivity.
      + punfold REL0. red in REL0. simpl in *.
        remember (VisF e k1) as ot. genobs m1 ot2.
        hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot; cycle 1.
        * gclo; econstructor; cycle -1; eauto; try reflexivity.
          rewrite (simpobs Heqot1), tau_eutt. reflexivity.
        * pclearbot. gstep. red. do 2 (simpobs; econstructor; eauto). intros.
          eapply MON; [|intros; gbase; eapply CIH; eauto].
          eapply CLOV.
          { intros. destruct PR, EQR. econstructor; cycle -1; eauto using eutt_trans. }
          econstructor; eauto.
          eapply MON; eauto. intros.
          econstructor; try reflexivity.
          gfinal. destruct PR; eauto.
      + eapply IHREL0; eauto.
        rewrite REL, <-stream_eta, tau_eutt. reflexivity.
      + gclo; econstructor; cycle -1; eauto; try reflexivity.
        rewrite (simpobs Heqot2), tau_eutt. reflexivity.
    - remember (VisF e k2) as ot. genobs t2 ot2.
      hinduction REL0 before CIH; intros; subst; try dependent destruction Heqot; cycle 1.
      + gclo; econstructor; cycle -1; eauto; try reflexivity.
        rewrite (simpobs Heqot2), tau_eutt. reflexivity.
      + pclearbot. gstep. red. simpobs. econstructor; eauto. intros.
        eapply MON; [|intros; gbase; eapply CIH; eauto].
        eapply CLOV.
        { intros. destruct PR, EQR. econstructor; cycle -1; eauto using eutt_trans. }
        econstructor; eauto.
        eapply MON; eauto. intros.
        econstructor; try reflexivity.
        gfinal. destruct PR; eauto.
    - gclo; econstructor; cycle -1; eauto; try reflexivity.
      rewrite (simpobs Heqot1), tau_eutt. reflexivity.
    - clear t' Heqot'. remember (TauF s2) as ot. genobs t2 ot2.
      hinduction REL before EQL; intros; subst; try inv Heqot; eauto; cycle 1.
      + gclo; econstructor; cycle -1; eauto; try reflexivity.
        rewrite (simpobs Heqot2), tau_eutt. reflexivity.
      + destruct REL; cycle 1.
        * gbase. apply CLOL. econstructor; eauto.
          apply CLOD. econstructor; eauto; try reflexivity.
          rewrite (simpobs Heqot2), tau_eutt. reflexivity.
        * eapply IHEQL; eauto.
          simpobs. econstructor; eauto.
          punfold H.
  Qed.

  Lemma euttVC_transL gH r:
    transL (euttVC gH r) <2= euttVC gH r.
  Proof.
    intros. eapply transL_closed; eauto using transU_compose, transLleU, transDleU with paco.
  Qed.
End EUTTG_Properties1.

Section EUTTG_Properties2.

  Lemma euttVC_transU gH r
        (CLOR: transU r <2= r):
    transU (euttVC gH r) <2= @euttVC gH r.
  Proof.
    intros. destruct PR.
    eapply euttVC_transL; eauto using transLleU, transDleU with paco.
    econstructor; eauto.
    eapply euttVC_flip. unfold flip.
    eapply euttVC_transL; eauto using transLleU, transDleU, transU_flip with paco.
    econstructor; eauto.
    apply euttVC_flip. eauto.
  Qed.

  Lemma euttG_transU_aux gH r
        (CLOR: transU r <2= r):
    transU (gupaco2 (bisim_ true true (euttVC gH)) transD r) <2=
    gupaco2 (bisim_ true true (euttVC gH)) transD r.
  Proof.
    intros. destruct PR.
    eapply transL_closed; eauto using euttVC_transL, transLleU, transDleU with paco.
    econstructor; eauto.
    apply euttG_flip. unfold flip.
    eapply transL_closed; eauto using euttVC_transL, transLleU, transDleU, transU_flip with paco.
    econstructor; eauto.
    apply euttG_flip. eauto.
  Qed.

  Lemma euttVC_gen gH r:
    transU (gupaco2 (bisim_ true true (euttVC gH)) transD (transU (r \2/ gH)))
    <2= euttVC gH r.
  Proof.
    intros. eapply euttG_transU_aux in PR; eauto using transU_compose.
    revert x0 x1 PR. gcofix CIH. intros.
    gunfold PR. apply rclo_transD in PR.
    gclo. eapply transD_mon; eauto. intros.
    destruct PR0; eauto with paco.
    gstep. red in H |- *. induction H; eauto.
    - econstructor. gbase. eapply CIH.
      eapply gupaco2_mon; eauto. intros.
      destruct PR0; eauto.
    - econstructor. intros. gbase. eapply CIH.
      red in REL. gupaco. eapply gupaco2_mon_gen; eauto with paco; intros.
      + eapply bisimF_mono; eauto with paco.
      + eapply euttG_transU_aux; eauto using transU_compose with paco.
        eapply transU_mon; eauto. intros.
        destruct PR1; [|eauto 7 with paco].
        eapply gupaco2_mon; eauto. intros.
        destruct PR1; eauto.
  Qed.

  Lemma euttG_gen rH rL gL gH:
    euttG rH rL (gL \2/ (transU rH \2/ rL)) gH <2= euttG rH rL gL gH.
  Proof.
    intros. destruct PR. econstructor.
    eapply gpaco2_gen_guard. eauto.
  Qed.

  Lemma euttG_cofix_aux: forall rH rL gL gH x,
      (x <2= euttG rH rL (gL \2/ x) (gH \2/ x)) -> (x <2= euttG rH rL gL gH).
  Proof.
    intros. apply euttG_gen.
    econstructor. revert x0 x1 PR. gcofix CIH.
    intros. apply H in PR. destruct PR.
    revert_until CIH. gcofix CIH. intros.
    apply gpaco2_dist in IN; eauto with paco.
    destruct IN; cycle 1.
    { apply rclo_transD in H0; eauto with paco.
      gclo. eapply transD_mon; eauto with paco.
    }
    assert (LEM: upaco2 (bisim_ true true (euttVC (gH \2/ x)))
                        (rclo2 transD ((gL \2/ x) \2/ (transU rH \2/ rL)))
                 <2= gpaco2 (bisim_ true true (euttVC gH)) transD r r).
    { intros m1 m2 [REL|REL].
      - gbase. apply CIH1.
        gpaco. gfinal. right.
        eapply paco2_mon; eauto. intros.
        apply rclo_transD in PR. gclo. eapply transD_mon; eauto. intros. gbase.
        repeat destruct PR0 as [PR0|PR0]; eauto.
      - apply rclo_transD in REL. gclo. eapply transD_mon; eauto. intros. gbase.
        repeat destruct PR as [PR|PR]; eauto.
    }
    punfold H0. gstep. red in H0 |- *.
    induction H0; eauto.
    red in REL. econstructor.
    eapply gupaco2_mon; eauto. intros.
    apply transU_dist in PR. destruct PR; eauto using transU_mon.
    eapply transU_mon; eauto. intros; destruct PR; eauto with paco.
  Qed.

End EUTTG_Properties2.

(* Proof of the exposed reasoning principles *)
Section EUTTG_principles.

  (* Make new hypotheses *)

  Lemma euttG_cofix rH rL gL gH x
        (OBG: forall gL' (INCL: gL <2= gL') (CIHL: x <2= gL') gH' (INCH: gH <2= gH') (CIHH: x <2= gH'), x <2= euttG rH rL gL' gH'):
    x <2= euttG rH rL gL gH.
  Proof.
    eapply euttG_cofix_aux; intros.
    eapply OBG; eauto.
  Qed.

  (* Process streams *)

  Lemma euttG_ret: forall rH rL gL gH,
      euttG rH rL gL gH Ret Ret.
  Proof.
    econstructor. gstep. econstructor.
  Qed.

  Lemma euttG_concat: forall rH rL gL gH t1 t2,
      concatC (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.
  Proof.
    econstructor. guclo bisim_clo_concat.
    destruct H. econstructor; eauto.
    intros. edestruct REL; eauto.
  Qed.

  Lemma euttG_transD: forall rH rL gL gH t1 t2,
      transD (euttG rH rL gL gH) t1 t2 -> euttG rH rL gL gH t1 t2.
  Proof.
    econstructor. guclo bisim_clo_trans.
    destruct H. econstructor; eauto.
    edestruct REL; eauto.
  Qed.

  (* Drop weak hypotheses for general rewriting *)

  Lemma euttG_drop rH rL gL gH t1 t2:
    euttG rH rH rH gH t1 t2 -> euttG rH rL gL gH t1 t2.
  Proof.
    intros. apply euttG_gen. destruct H. econstructor.
    eapply gpaco2_mon; intros; eauto; [destruct PR|]; eauto using transU_id.
  Qed.

  Lemma euttG_transU rH gH t1 t2:
    transU (euttG rH rH rH gH) t1 t2 -> euttG rH rH rH gH t1 t2.
  Proof.
    intros. apply euttG_gen.
    cut (gupaco2 (bisim_ true true (euttVC gH)) transD (transU rH) t1 t2).
    { intros. econstructor. eapply gpaco2_mon; eauto. }
    eapply euttG_transU_aux; eauto using transU_compose.
    eapply transU_mon; eauto. intros. destruct PR.
    eapply gpaco2_mon; eauto; intros;
      repeat destruct PR as [PR|PR]; eauto using transU_id.
  Qed.

  (* Make a weakly guarded progress *)
  (* Under a Tau, the low guarded predicate becomes regularly accessible *)
  Lemma euttG_tau: forall rH rL gL gH t1 t2,
      euttG rH gL gL gH t1 t2 -> euttG rH rL gL gH (Tau t1) (Tau t2).
  Proof.
    intros. apply euttG_gen. destruct H. econstructor.
    gstep. econstructor.
    eapply gpaco2_mon; eauto; intros; repeat destruct PR as [PR|PR]; eauto.
  Qed.
  (* Make a strongly guarded progress *)
  (* Under a Vis, the strongly guarded knowledge becomes available anywhere *)
  Lemma euttG_vis: forall rH rL gL gH (e: nat) k1 k2,
      (euttG gH gH gH gH k1 k2) -> euttG rH rL gL gH (Vis e k1) (Vis e k2).
  Proof.
    econstructor. gstep. econstructor. intros.
    specialize H. destruct H.
    apply euttVC_gen. econstructor; try reflexivity.
    eapply gpaco2_mon_gen; eauto; intros; repeat destruct PR as [PR|PR];
      eauto using gpaco2_clo, transDleU, transU_mon with paco.
  Qed.

  (* Use available hypotheses *)
  (* The regular knowledges are always available *)
  Lemma euttG_base: forall rH rL gL gH t1 t2,
      rH t1 t2 \/ rL t1 t2 -> euttG rH rL gL gH t1 t2.
  Proof.
    intros. econstructor. gbase.
    destruct H; eauto using transU_id.
  Qed.

  (**
   Correctness
   **)

  Lemma euttG_le_eutt:
    euttG bot2 bot2 bot2 bot2 <2= eutt.
  Proof.
    intros. destruct PR.
    assert(paco2 (bisim_ true true (euttVC bot2)) bot2 x0 x1).
    { eapply gpaco2_init; eauto with paco.
      eapply gpaco2_mon; eauto; intros;
        repeat destruct PR as [PR|PR]; destruct PR; contradiction.
    }
    clear IN.
    revert x0 x1 H. pcofix CIH. intros.
    punfold H0. pstep. unfold_bisim.
    induction H0; pclearbot; eauto.
    econstructor; intros.
    right. apply CIH.
    ginit. gupaco. eapply gupaco2_mon_gen; eauto with paco; intros.
    - eapply bisimF_mono; eauto with paco.
    - apply euttG_transU_aux.
      { intros. destruct PR0; contradiction. }
      eapply transU_mon; eauto. intros.
      pclearbot. gfinal. eauto.
  Qed.

  Lemma eutt_le_euttG rH rL gL gH:
    eutt <2= euttG rH rL gL gH.
  Proof.
    intros. econstructor. econstructor. apply rclo2_base. left.
    eapply paco2_mon_bot; eauto; intros.
    eapply bisimF_mono; eauto with paco.
  Qed.

End EUTTG_principles.

(* We wrap the interface into some Ltac sugar to make it user friendly *)

Require Import Paco.pacotac_internal.

Tactic Notation "ecofix" ident(CIH) "with" ident(gL) ident(gH) :=
  repeat red;
  paco_pre2;
  eapply euttG_cofix;
  paco_post2 CIH with gL;
  paco_post2 CIH with gH.

Tactic Notation "ecofix" ident(CIH) := ecofix CIH with gL gH.

Ltac einit := repeat red; under_forall ltac:(eapply euttG_le_eutt; eauto with paco).
Ltac efinal := repeat red; under_forall ltac:(eapply eutt_le_euttG; eauto with paco).
Ltac ebase := repeat red; under_forall ltac:(eapply euttG_base; eauto with paco).
Ltac eret := repeat red; under_forall ltac:(eapply euttG_ret; eauto with paco).
Ltac etau := repeat red; under_forall ltac:(eapply euttG_tau; eauto with paco).
Ltac evis := repeat red; under_forall ltac:(eapply euttG_vis; eauto with paco).
Ltac estep := first [eret|etau|evis].
Ltac econcat := repeat red; under_forall ltac:(eapply euttG_concat; eauto with paco).
Ltac edrop := repeat red; under_forall ltac:(eapply euttG_drop; eauto with paco).

Hint Resolve euttG_ret : paco.
Hint Resolve euttG_tau : paco.
Hint Resolve euttG_vis : paco.
Hint Resolve euttG_base : paco.
Hint Resolve euttG_le_eutt: paco.

Global Instance euttG_reflexive rH rL gL gH:
  Reflexive (euttG rH rL gL gH).
Proof.
  red; intros. efinal. reflexivity.
Qed.

Global Instance euttG_cong_eutt rH gH:
  Proper (eutt ==> eutt ==> flip impl)
         (euttG rH rH rH gH).
Proof.
  repeat intro. eapply euttG_transU. eauto.
Qed.

Global Instance euttG_cong_euttge rH rL gL gH:
  Proper (euttge ==> euttge ==> flip impl)
         (euttG rH rL gL gH).
Proof.
  repeat intro. eapply euttG_transD. eauto.
Qed.

Global Instance euttG_cong_eq rH rL gL gH:
  Proper (eq_stream ==> eq_stream ==> flip impl)
         (euttG rH rL gL gH).
Proof.
  repeat intro. eapply euttG_cong_euttge; eauto; apply eq_sub_bisim; eauto.
Qed.

Global Instance eutt_cong_eutt :
  Proper (eutt ==> eutt ==> flip impl)
         (bisim true true).
Proof.
  einit. intros. rewrite H0, H1. efinal.
Qed.

Global Instance eutt_cong_euttge :
  Proper (euttge ==> euttge ==> flip impl)
         (bisim true true).
Proof.
  einit. intros. rewrite H0, H1. efinal.
Qed.

Global Instance eutt_cong_eq :
  Proper (eq_stream ==> eq_stream ==> flip impl)
         (bisim true true).
Proof.
  einit. intros. rewrite H0, H1. efinal.
Qed.

