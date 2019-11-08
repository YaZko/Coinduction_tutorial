Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco7 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section RClo.

Inductive rclo7 (clo: rel->rel) (r: rel): rel :=
| rclo7_base
    x0 x1 x2 x3 x4 x5 x6
    (IN: r x0 x1 x2 x3 x4 x5 x6):
    @rclo7 clo r x0 x1 x2 x3 x4 x5 x6
| rclo7_clo'
    r' x0 x1 x2 x3 x4 x5 x6
    (LE: r' <7= rclo7 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6):
    @rclo7 clo r x0 x1 x2 x3 x4 x5 x6
.           

Lemma rclo7_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6
      (IN: @rclo7 clo r x0 x1 x2 x3 x4 x5 x6)
      (LEclo: clo <8= clo')
      (LEr: r <7= r') :
  @rclo7 clo' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo7_mon clo:
  monotone7 (rclo7 clo).
Proof.
  repeat intro. eapply rclo7_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo7_clo clo r:
  clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo7_rclo clo r:
  rclo7 clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo7_compose clo r:
  rclo7 (rclo7 clo) r <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - apply rclo7_base, IN.
  - apply rclo7_rclo.
    eapply rclo7_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Variant gpaco7 clo r rg x0 x1 x2 x3 x4 x5 x6 : Prop :=
| gpaco7_intro (IN: @rclo7 clo (paco7 (compose gf (rclo7 clo)) (rg \7/ r) \7/ r) x0 x1 x2 x3 x4 x5 x6)
.

Definition gupaco7 clo r := gpaco7 clo r r.

Lemma gpaco7_def_mon clo : monotone7 (compose gf (rclo7 clo)).
Proof.
  eapply monotone7_compose. apply gf_mon. apply rclo7_mon.
Qed.

Hint Resolve gpaco7_def_mon : paco.

Lemma gpaco7_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6
      (IN: @gpaco7 clo r rg x0 x1 x2 x3 x4 x5 x6)
      (LEr: r <7= r')
      (LErg: rg <7= rg'):
  @gpaco7 clo r' rg' x0 x1 x2 x3 x4 x5 x6.
Proof.
  destruct IN. econstructor.
  eapply rclo7_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco7_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco7_mon clo r r' x0 x1 x2 x3 x4 x5 x6
      (IN: @gupaco7 clo r x0 x1 x2 x3 x4 x5 x6)
      (LEr: r <7= r'):
  @gupaco7 clo r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply gpaco7_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco7_base clo r rg: r <7= gpaco7 clo r rg.
Proof.
  econstructor. apply rclo7_base. right. apply PR.
Qed.

Lemma gpaco7_gen_guard  clo r rg:
  gpaco7 clo r (rg \7/ r) <7= gpaco7 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo7_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco7_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco7_rclo clo r rg:
  rclo7 clo r <7= gpaco7 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo7_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco7_clo clo r rg:
  clo r <7= gpaco7 clo r rg.
Proof.
  intros. apply gpaco7_rclo. eapply rclo7_clo', PR.
  apply rclo7_base.
Qed.

Lemma gpaco7_gen_rclo clo r rg:
  gpaco7 (rclo7 clo) r rg <7= gpaco7 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo7_compose.
  eapply rclo7_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco7_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo7_compose. apply PR.
Qed.

Lemma gpaco7_step_gen clo r rg:
  gf (gpaco7 clo (rg \7/ r) (rg \7/ r)) <7= gpaco7 clo r rg.
Proof.
  intros. econstructor. apply rclo7_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo7_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco7_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco7_step clo r rg:
  gf (gpaco7 clo rg rg) <7= gpaco7 clo r rg.
Proof.
  intros. apply gpaco7_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco7_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco7_final clo r rg:
  (r \7/ paco7 gf rg) <7= gpaco7 clo r rg.
Proof.
  intros. destruct PR. apply gpaco7_base, H.
  econstructor. apply rclo7_base.
  left. eapply paco7_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo7_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco7_unfold clo r rg:
  gpaco7 clo r rg <7= rclo7 clo (gf (gupaco7 clo (rg \7/ r)) \7/ r).
Proof.
  intros. destruct PR.
  eapply rclo7_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco7_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo7_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco7_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco7_cofix clo r rg 
      l (OBG: forall rr (INC: rg <7= rr) (CIH: l <7= rr), l <7= gpaco7 clo r rr):
  l <7= gpaco7 clo r rg.
Proof.
  assert (IN: l <7= gpaco7 clo r (rg \7/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo7_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco7_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo7_rclo. eapply rclo7_mon. apply PR.
  intros. destruct PR0.
  - apply rclo7_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo7_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo7_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo7_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco7_gupaco clo r rg:
  gupaco7 clo (gpaco7 clo r rg) <7= gpaco7 clo r rg.
Proof.
  eapply gpaco7_cofix.
  intros. destruct PR. econstructor.
  apply rclo7_rclo. eapply rclo7_mon. apply IN.
  intros. destruct PR.
  - apply rclo7_base. left.
    eapply paco7_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo7_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo7_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco7_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco7_gpaco clo r rg:
  gpaco7 clo (gpaco7 clo r rg) (gupaco7 clo (rg \7/ r)) <7= gpaco7 clo r rg.
Proof.
  intros. apply gpaco7_unfold in PR.
  econstructor. apply rclo7_rclo. eapply rclo7_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo7_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 x6 H. intros.
  cut (@gupaco7 clo (rg \7/ r) x0 x1 x2 x3 x4 x5 x6).
  { intros. destruct H. eapply rclo7_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco7_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco7_gupaco. eapply gupaco7_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco7_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco7_uclo uclo clo r rg 
      (LEclo: uclo <8= gupaco7 clo) :
  uclo (gpaco7 clo r rg) <7= gpaco7 clo r rg.
Proof.
  intros. apply gpaco7_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco7_weaken  clo r rg:
  gpaco7 (gupaco7 clo) r rg <7= gpaco7 clo r rg.
Proof.
  intros. apply gpaco7_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco7_base, H.
    apply gpaco7_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 H.
    eapply gpaco7_cofix. intros.
    apply gpaco7_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco7_base, H.
      apply gpaco7_step. eapply gf_mon. apply H.
      intros. apply gpaco7_base. apply CIH.
      eapply gupaco7_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco7_gupaco.
      eapply gupaco7_mon. apply IN. apply H.
  - apply gpaco7_gupaco.
    eapply gupaco7_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco7_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco7_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r r' rg rg'
      (IN: @gpaco7 gf clo r rg x0 x1 x2 x3 x4 x5 x6)
      (gf_mon: monotone7 gf)
      (LEgf: gf <8= gf')
      (LEclo: clo <8= clo')
      (LEr: r <7= r')
      (LErg: rg <7= rg') :
  @gpaco7 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply gpaco7_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo7_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco7_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo7_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco7_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r' rg'
      (IN: @gpaco7 gf clo bot7 bot7 x0 x1 x2 x3 x4 x5 x6)
      (gf_mon: monotone7 gf)
      (LEgf: gf <8= gf')
      (LEclo: clo <8= clo'):
  @gpaco7 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply gpaco7_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco7_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r r'
      (IN: @gupaco7 gf clo r x0 x1 x2 x3 x4 x5 x6)
      (gf_mon: monotone7 gf)
      (LEgf: gf <8= gf')
      (LEclo: clo <8= clo')
      (LEr: r <7= r'):
  @gupaco7 gf' clo' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply gpaco7_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Structure compatible7 (clo: rel -> rel) : Prop :=
  compat7_intro {
      compat7_mon: monotone7 clo;
      compat7_compat : forall r,
          clo (gf r) <7= gf (clo r);
    }.

Structure wcompatible7 clo : Prop :=
  wcompat7_intro {
      wcompat7_mon: monotone7 clo;
      wcompat7_wcompat : forall r,
          clo (gf r) <7= gf (gupaco7 gf clo r);
    }.

Lemma rclo7_dist clo
      (MON: monotone7 clo)
      (DIST: forall r1 r2, clo (r1 \7/ r2) <7= (clo r1 \7/ clo r2)):
  forall r1 r2, rclo7 clo (r1 \7/ r2) <7= (rclo7 clo r1 \7/ rclo7 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo7_base, H.
  + assert (REL: clo (rclo7 clo r1 \7/ rclo7 clo r2) x0 x1 x2 x3 x4 x5 x6).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo7_clo, H0.
Qed.

Lemma rclo7_compat clo
      (COM: compatible7 clo):
  compatible7 (rclo7 clo).
Proof.
  econstructor.
  - apply rclo7_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo7_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo7_clo. apply PR.
Qed.

Lemma rclo7_wcompat clo
      (COM: wcompatible7 clo):
  wcompatible7 (rclo7 clo).
Proof.
  econstructor.
  - apply rclo7_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco7_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco7_gupaco. apply gf_mon.
        eapply gupaco7_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        eapply rclo7_clo'. apply rclo7_base. apply PR0.
Qed.

Lemma compat7_wcompat clo
      (CMP: compatible7 clo):
  wcompatible7 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco7_clo, PR0. 
Qed.

Lemma wcompat7_compat clo
      (WCMP: wcompatible7 clo) :
  compatible7 (gupaco7 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco7_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco7_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco7_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco7_gupaco. apply gf_mon.
      eapply gupaco7_mon. apply PR.
      intros. apply gpaco7_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco7_base, PR1.
  - eapply gf_mon, gpaco7_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat7_union clo1 clo2
      (WCMP1: wcompatible7 clo1)
      (WCMP2: wcompatible7 clo2):
  wcompatible7 (clo1 \8/ clo2).
Proof.
  econstructor.
  - apply monotone7_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco7_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco7_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Lemma gpaco7_compat_init clo
      (CMP: compatible7 gf clo):
  gpaco7 gf clo bot7 bot7 <7= paco7 gf bot7.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo7_rclo, PR]. 
  apply compat7_compat with (gf:=gf). apply rclo7_compat. apply gf_mon. apply CMP.
  eapply rclo7_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco7_def_mon, gf_mon].
  eapply gpaco7_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco7_init clo
      (WCMP: wcompatible7 gf clo):
  gpaco7 gf clo bot7 bot7 <7= paco7 gf bot7.
Proof.
  intros. eapply gpaco7_compat_init.
  - apply wcompat7_compat, WCMP. apply gf_mon.
  - eapply gpaco7_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco7_clo, PR0.
Qed.

Lemma gpaco7_unfold_bot clo
      (WCMP: wcompatible7 gf clo):
  gpaco7 gf clo bot7 bot7 <7= gf (gpaco7 gf clo bot7 bot7).
Proof.
  intros. apply gpaco7_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco7_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Lemma gpaco7_dist clo r rg
      (CMP: wcompatible7 gf clo)
      (DIST: forall r1 r2, clo (r1 \7/ r2) <7= (clo r1 \7/ clo r2)):
  gpaco7 gf clo r rg <7= (paco7 gf (rclo7 clo (rg \7/ r)) \7/ rclo7 clo r).
Proof.
  intros. apply gpaco7_unfold in PR; [|apply gf_mon].
  apply rclo7_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 H.
  pcofix CIH; intros.
  apply rclo7_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco7_unfold in PR; [|apply gf_mon].
  apply rclo7_compose in PR.
  apply rclo7_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo7_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco7_gupaco. apply gf_mon.
    apply gpaco7_gen_rclo. apply gf_mon.
    eapply gupaco7_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo7 clo (rclo7 clo (gf (gupaco7 gf clo ((rg \7/ r) \7/ (rg \7/ r))) \7/ (rg \7/ r))) x0 x1 x2 x3 x4 x5 x6).
    { eapply rclo7_mon. apply H. intros. apply gpaco7_unfold in PR. apply PR. apply gf_mon. }
    apply rclo7_rclo in REL.
    apply rclo7_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo7_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco7_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco7_dist_reverse clo r rg:
  (paco7 gf (rclo7 clo (rg \7/ r)) \7/ rclo7 clo r) <7= gpaco7 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco7_rclo. apply H.
  - econstructor. apply rclo7_base. left.
    revert x0 x1 x2 x3 x4 x5 x6 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo7_base. right. apply CIH, H.
    + eapply rclo7_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Inductive cpn7 (r: rel) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| cpn7_intro
    clo
    (COM: compatible7 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6)
.

Lemma cpn7_mon: monotone7 cpn7.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat7_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn7_greatest: forall clo (COM: compatible7 gf clo), clo <8= cpn7.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn7_compat: compatible7 gf cpn7.
Proof.
  econstructor; [apply cpn7_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat7_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn7_wcompat: wcompatible7 gf cpn7.
Proof. apply compat7_wcompat, cpn7_compat. apply gf_mon. Qed.

Lemma cpn7_gupaco:
  gupaco7 gf cpn7 <8= cpn7.
Proof.
  intros. eapply cpn7_greatest, PR. apply wcompat7_compat. apply gf_mon. apply cpn7_wcompat.
Qed.

Lemma cpn7_cpn r:
  cpn7 (cpn7 r) <7= cpn7 r.
Proof.
  intros. apply cpn7_gupaco, gpaco7_gupaco, gpaco7_clo. apply gf_mon.
  eapply cpn7_mon, gpaco7_clo. apply PR.
Qed.

Lemma cpn7_base r:
  r <7= cpn7 r.
Proof.
  intros. apply cpn7_gupaco. apply gpaco7_base, PR.
Qed.

Lemma cpn7_clo
      r clo (LE: clo <8= cpn7):
  clo (cpn7 r) <7= cpn7 r.
Proof.
  intros. apply cpn7_cpn, LE, PR.
Qed.

Lemma cpn7_step r:
  gf (cpn7 r) <7= cpn7 r.
Proof.
  intros. apply cpn7_gupaco. apply gpaco7_step. apply gf_mon.
  eapply gf_mon, gpaco7_clo. apply PR.
Qed.

Lemma cpn7_uclo uclo
      (MON: monotone7 uclo)
      (WCOM: forall r, uclo (gf r) <7= gf (gupaco7 gf (uclo \8/ cpn7) r)):
  uclo <8= gupaco7 gf cpn7.
Proof.
  intros. apply gpaco7_clo.
  exists (gupaco7 gf (uclo \8/ cpn7)).
  - apply wcompat7_compat. apply gf_mon.
    econstructor.
    + apply monotone7_union. apply MON. apply cpn7_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat7_compat with (gf:=gf) in H; [| apply cpn7_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco7_clo. right. apply PR0.
  - apply gpaco7_clo. left. apply PR.
Qed.

End Companion.

End GeneralizedPaco7.

Hint Resolve gpaco7_def_mon : paco.
Hint Unfold gupaco7 : paco.
Hint Resolve gpaco7_base : paco.
Hint Resolve gpaco7_step : paco.
Hint Resolve gpaco7_final : paco.
Hint Resolve rclo7_base : paco.
Hint Constructors gpaco7 : paco.
