Require Import Common.Common.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.Inst.

Require Import Omega.
Require Import Min.

Section ValrelInversion.

  Local Ltac crush :=
    repeat
      (simpl;
       try assumption;
       crushOfType;
       repeat crushTyping;
       repeat crushStlcSyntaxMatchH;
       repeat crushUtlcSyntaxMatchH;
       repeat crushUtlcScopingMatchH;
       try subst;
       destruct_conjs;
       repeat match goal with
                  [ |- _ ∧ _ ] => split
              end;
       eauto
      ); try omega.

  Lemma valrel_ptprod_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptprod τ₁ τ₂) vs vu →
    exists vs₁ vs₂ vu₁ vu₂,
      (vs = S.pair vs₁ vs₂ ∧ vu = U.pair vu₁ vu₂ ∧
       OfType τ₁ vs₁ vu₁ ∧
       OfType τ₂ vs₂ vu₂ ∧
       ∀ w', w' < w → valrel d w' τ₁ vs₁ vu₁ ∧ valrel d w' τ₂ vs₂ vu₂).
  Proof.
    intros vr.
    destruct (valrel_implies_Value vr) as [vvs vvu].
    destruct (OfType_inversion_ptprod (valrel_implies_OfType vr))
      as (ts1' & tu1' & ts2' & tu2' & Hvs & Hvu & oft1 & oft2).
    exists ts1', ts2', tu1', tu2'; do 4 (split; auto).
    rewrite -> valrel_fixp in vr; subst vs vu.
    unfold valrel' in vr; crush.
  Qed.

  Lemma valrel_ptsum_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptsum τ₁ τ₂) vs vu →
    exists vs' vu',
      (vs = S.inl vs' ∧ vu = U.inl vu' ∧
       OfType τ₁ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₁ vs' vu') ∨
      (vs = S.inr vs' ∧ vu = U.inr vu' ∧
       OfType τ₂ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₂ vs' vu').
  Proof.
    intros vr.
    rewrite -> valrel_fixp in vr; destruct vr as [oft sumrel];
    cbn in *; apply OfType_inversion_ptsum in oft;
    destruct oft as (tsb & tub & Hvs); intuition; crush.
    - exists tsb, tub; crush.
    - exists tsb, tub; crush.
  Qed.

  Lemma valrel_ptarr_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptarr τ₁ τ₂) vs vu →
    ∃ tsb tub,
      vs = S.abs (repEmul τ₁) tsb ∧ vu = U.abs tub ∧
      ⟪ empty ▻ repEmul τ₁ ⊢ tsb : repEmul τ₂ ⟫ ∧
      ∀ w' vs' vu',
        w' < w → valrel d w' τ₁ vs' vu' →
        termrel d w' τ₂ (tsb[beta1 vs']) (tub[beta1 vu']).
  Proof.
    intros vr.
    destruct (valrel_implies_Value vr) as [vvs vvu].
    destruct (OfType_inversion_ptarr (valrel_implies_OfType vr))
      as (tsb & tub & Hvs & Hvu & wtsb).
    exists tsb, tub; do 2 (split; auto).
    rewrite -> valrel_fixp in vr; subst vs vu.
    unfold valrel' in vr; unfold termrel; crush.
  Qed.

End ValrelInversion.
