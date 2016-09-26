Require Import UVal.UVal.
Require Import Utlc.LemmasScoping.
Require Import Utlc.SpecSyntax.
Require Import Stlc.SpecSyntax.
Require Import Stlc.Inst.
Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import LogRel.LemmasInversion.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.PseudoType.
Require Import BackTrans.UpgradeDowngrade.
Require Import Omega.


Section Intro.
  Definition inUnitDwn (n : nat) (t : Tm) := app (downgrade n 1) (inUnit n t).
  Definition inBoolDwn (n : nat) (t : Tm) := app (downgrade n 1) (inBool n t).
  Definition inProdDwn (n : nat) (t : Tm) := app (downgrade n 1) (inProd n t).
  Definition inArrDwn (n : nat) (t : Tm) := app (downgrade n 1) (inArr n t).
  Definition inSumDwn (n : nat) (t : Tm) := app (downgrade n 1) (inSum n t).
End Intro.

Section IntroProps.
  Lemma termrel_inUnitDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w ptunit vs vu →
    termrel d w (pEmulDV n p) (inUnitDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inUnitDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inUnit'; trivial.
  Qed.

  Lemma termrel_inBoolDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w ptbool vs vu →
    termrel d w (pEmulDV n p) (inBoolDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inBoolDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inBool'; trivial.
  Qed.

  Lemma termrel_inProdDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w (ptprod (pEmulDV n p) (pEmulDV n p)) vs vu →
    termrel d w (pEmulDV n p) (inProdDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inProdDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inProd''; trivial.
  Qed.

  Lemma termrel_inSumDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w (ptsum (pEmulDV n p) (pEmulDV n p)) vs vu →
    termrel d w (pEmulDV n p) (inSumDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inProdDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inSum''; trivial.
  Qed.

  Lemma termrel_inArrDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w (ptarr (pEmulDV n p) (pEmulDV n p)) vs vu →
    termrel d w (pEmulDV n p) (inArrDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inArrDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inArr; trivial.
  Qed.
End IntroProps.

Section Destruct.
  Definition caseUnitDwn (n : nat) (t : Tm) := app (downgrade n 1) (inUnit n t).
  Definition inBoolDwn (n : nat) (t : Tm) := app (downgrade n 1) (inBool n t).
  Definition inProdDwn (n : nat) (t : Tm) := app (downgrade n 1) (inProd n t).
  Definition inArrDwn (n : nat) (t : Tm) := app (downgrade n 1) (inArr n t).
  Definition inSumDwn (n : nat) (t : Tm) := app (downgrade n 1) (inSum n t).
End Destruct.

Section DestructProps.
End DestructProps.