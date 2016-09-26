Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import BackTrans.UValHelpers.
Require Import Stlc.SpecTyping.
Require Import Stlc.StlcOmega.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import Omega.
Require Import Db.Lemmas.
Require Import UVal.UVal.
Require Utlc.Fix.

Fixpoint emulate (n : nat) (t : U.UTm) : S.Tm :=
  match t with
    | U.wrong => stlcOmega (UVal n)
    | U.var i => S.var i
    | U.abs t => inArrDwn n (S.abs (UVal n) (emulate n t))
    | U.app t₁ t₂ => S.unit
    | U.unit => inUnitDwn n S.unit
    | U.true => inBoolDwn n S.true
    | U.false => inBoolDwn n S.false
    | U.ite t₁ t₂ t₃ => S.unit
    | U.pair t₁ t₂ => inProdDwn n (S.pair (emulate n t₁) (emulate n t₂))
    | U.proj₁ t => S.unit
    | U.proj₂ t => S.unit
    | U.inl t => inSumDwn n (emulate n t)
    | U.inr t => inSumDwn n (emulate n t)
    | U.caseof t₁ t₂ t₃ => S.unit
    | U.seq t₁ t₂ => S.unit
  end.
