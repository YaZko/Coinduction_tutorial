(**
   This file is part of the supplementary material accompanying the
   submission to CPP'20:
   _An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction_
 *)
(**
   These few examples illustrates the shortcoming of paco and the use of euttG.
*)
(* begin hide *)
From Paco Require Import paco.
From Coq Require Import
     Nat
     Morphisms
     Program.

From EuttG Require Import stream euttG.
(* end hide *)

Section Examples.

  Open Scope stream_scope.

  Notation euttF := (bisim_ true true).

  Lemma ex_incr f1 f2 g1 g2
        (EQF1: forall n, f1 n = Tau (Vis n (f2 n)))
        (EQF2: forall n, f2 n = if n =? 0
                                then Tau (f1 (n+1))
                                else Tau (f2 (n+1)))
        (EQG1: forall n, g1 n = Vis n (g2 n))
        (EQG2: forall n, g2 n = if n =? 0
                                then Tau (g1 (n+1))
                                else Tau (g2 (n+1))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    do 2 red. pcofix CIH1. intros.
    rewrite EQF1, EQG1.
    pstep; do 2 econstructor; repeat red.
    left. revert n. pcofix CIH2. intros.
    rewrite EQF2, EQG2.
    destruct (n =? 0); simpl.
    - pstep; econstructor; repeat red.
      right. apply CIH1.
    - pstep; econstructor; repeat red.
      right. apply CIH2.
  Qed.

  Lemma ex_incr2_awkward f1 f2 g1 g2
        (EQF1: forall n, f1 n = Tau (Vis n (f2 n)))
        (EQF2: forall n, f2 n = if n =? 0
                                then (* Tau *) (f1 (n+1))
                                else Tau (f2 (n+1)))
        (EQG1: forall n, g1 n = Vis n (g2 n))
        (EQG2: forall n, g2 n = if n =? 0
                                then (* Tau *) (g1 (n+1))
                                else Tau (g2 (n+1))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    pcofix CIH1. intros.
    rewrite EQF1, EQG1.
    pstep; do 2 econstructor; repeat red.
    left.
    revert n. pcofix CIH2. intros.
    rewrite EQF2, EQG2.
    destruct (n =? 0); simpl.
    - (* We can't use CIH1 here *)
      (* begin unnecessary reasoning *)
      rewrite EQF1, EQG1.
      pstep; do 2 econstructor; repeat red.
      right. apply CIH2.
    (* end unnecessary reasoning *)
    - pstep; econstructor; repeat red.
      right. apply CIH2.
  Qed.

  Lemma ex_incr2 f1 f2 g1 g2
        (EQF1: forall n, f1 n = Tau (Vis n (f2 n)))
        (EQF2: forall n, f2 n = if n =? 0
                                then (* Tau *) (f1 (n+1))
                                else Tau (f2 (n+1)))
        (EQG1: forall n, g1 n = Vis n (g2 n))
        (EQG2: forall n, g2 n = if n =? 0
                                then (* Tau *) (g1 (n+1))
                                else Tau (g2 (n+1))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    ginit. gcofix CIH1. intros.
    rewrite EQF1, EQG1.
    gstep; do 2 econstructor; repeat red.
    revert n. gcofix CIH2. intros.
    rewrite EQF2, EQG2.
    destruct n; simpl.
    - gbase. apply CIH1.
    - gstep; econstructor; repeat red.
      gbase. apply CIH2.
  Qed.

  Lemma ex_upto h1 h2 f1 f2 g1 g2
        (EQH: forall n, eutt (h1 n) (h2 n))
        (EQF1: forall n, f1 n ≳ (h1 n ;; Vis n (f2 n)))
        (EQF2: forall n, f2 n ≳ if n =? 0
                                then f1 (n+1)
                                else Tau (f2 (n+1)))
        (EQG1: forall n, g1 n ≳ (h2 n ;; Vis n (g2 n)))
        (EQG2: forall n, g2 n ≳ if n =? 0
                                then g1 (n+1)
                                else Tau (g2 (n+1))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    ginit. gcofix CIH1. intros.
    (* guclo bisim_clo_trans. econstructor. *)
    (* { eapply EQF1. } *)
    (* { eapply EQG1. } *)
    rewrite EQF1, EQG1.
    guclo bisim_clo_concat. econstructor.
    { apply EQH. }
    gstep; econstructor; repeat red.
    revert n. gcofix CIH2. intros.
    guclo bisim_clo_trans. econstructor.
    { eapply EQF2. }
    { eapply EQG2. }
    destruct n; simpl.
    - gbase. apply CIH1.
    - gstep; econstructor; repeat red.
      gbase. apply CIH2.
  Qed.

  Lemma ex_upto' h1 h2 f1 f2 g1 g2
        (EQH: forall n, eutt (h1 n) (h2 n))
        (EQF1: forall n, f1 n ≳ (h1 n ;; Vis n (f2 n)))
        (EQF2: forall n, f2 n ≳ if n =? 0
                                then f1 (n+1)
                                else Tau (f2 (n+1)))
        (EQG1: forall n, g1 n ≳ (h2 n ;; Vis n (g2 n)))
        (EQG2: forall n, g2 n ≳ if n =? 0
                                then g1 (n+1)
                                else Tau (g2 (n+1))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    ginit. gcofix CIH1. intros.
    guclo bisim_clo_trans. econstructor.
    { eapply EQF1. }
    { eapply EQG1. }
    guclo bisim_clo_concat. econstructor.
    { apply EQH. }
    gstep; econstructor; repeat red.
    revert n. gcofix CIH2. intros.
    guclo bisim_clo_trans. econstructor.
    { eapply EQF2. }
    { eapply EQG2. }
    destruct n; simpl.
    - gbase. apply CIH1.
    - gstep; econstructor; repeat red.
      gbase. apply CIH2.
  Qed.

  Lemma ex_upto_rewrite h1 h2 f1 f2 g1 g2
        (EQH: forall n, eutt (h1 n) (h2 n))
        (EQF1: forall n, f1 n ≳ (h1 n ;; Vis n (f2 n)))
        (EQF2: forall n, f2 n ≳ if n =? 0
                                then f1 (n+1)
                                else Tau (f2 (n+1)))
        (EQG1: forall n, g1 n ≳ (h2 n ;; Vis n (g2 n)))
        (EQG2: forall n, g2 n ≳ if n =? 0
                           then g1 (n+1)
                           else Tau (g2 (n+1))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    ginit. gcofix CIH1. intros.
    rewrite EQF1, EQG1.
    guclo bisim_clo_concat. econstructor. { apply EQH. }
                                       gstep; econstructor; repeat red.
    revert n. gcofix CIH2. intros.
    rewrite EQF2, EQG2.
    destruct n; simpl.
    - gbase. apply CIH1.
    - gstep; econstructor; repeat red.
      gbase. apply CIH2.
  Qed.

  (* Example illustrating the rewriting by directed eutt *)
  Lemma ex_eutt h1 h2 f1 f2 g1 g2
        (EQH: forall n, eutt (h1 n) (h2 n))
        (EQF1: forall n, eutt (f1 n) (h1 n ;; Vis n (f2 n)))
        (EQF2: forall n, f2 n ≳ if n =? 0
                           then f1 (n+1)
                           else Tau (f2 (n+1)))
        (EQG1: forall n, eutt (g1 n) ((h2 n ;; Vis n (g2 n))))
        (EQG2: forall n, g2 n ≳ if n =? 0
                           then g1 (n+1)
                           else Tau (g2 (n+1))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    einit. ecofix CIH1. intros.
    edrop. rewrite EQF1, EQG1.
    econcat. econstructor.
    { apply EQH. }
    estep.
    revert n. ecofix CIH2. intros.
    rewrite EQF2, EQG2.
    destruct n; simpl.
    - ebase.
    - estep.
  Qed.

  (* The same statement assuming eutt is incorrect, and indeed the rewriting up
  to undirected eutt has correctly dropped too much information to conclude *)
  Lemma ex_eutt_failed h1 h2 f1 f2 g1 g2
        (EQH: forall n, eutt (h1 n) (h2 n))
        (EQF1: forall n, eutt (f1 n) (h1 n ;; Vis n (f2 n)))
        (EQF2: forall n, eutt (f2 n) (if n =? 0
                                 then f1 (n+1)
                                 else Tau (f2 (n+1))))
        (EQG1: forall n, eutt (g1 n) ((h2 n ;; Vis n (g2 n))))
        (EQG2: forall n, eutt (g2 n) (if n =? 0
                                 then g1 (n+1)
                                 else Tau (g2 (n+1)))):
    forall n, eutt (f1 n) (g1 n).
  Proof.
    einit. ecofix CIH1. intros.
    edrop. rewrite EQF1, EQG1.
    econcat. econstructor.
    { apply EQH. }
    estep.
    revert n. ecofix CIH2. intros.
    edrop. rewrite EQF2, EQG2.
    destruct n; simpl.
    - ebase.
    - estep. (* We (rightfully) cannot conclude! *)
  Abort.

End Examples.
