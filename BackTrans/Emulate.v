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
    | U.app t₁ t₂ => S.app (caseArrUp n (emulate n t₁)) (emulate n t₂)
    | U.unit => inUnitDwn n S.unit
    | U.true => inBoolDwn n S.true
    | U.false => inBoolDwn n S.false
    | U.ite t₁ t₂ t₃ => S.ite (caseBoolUp n (emulate n t₁)) (emulate n t₂) (emulate n t₃)
    | U.pair t₁ t₂ => inProdDwn n (S.pair (emulate n t₁) (emulate n t₂))
    | U.proj₁ t => S.proj₁ (caseProdUp n (emulate n t))
    | U.proj₂ t => S.proj₂ (caseProdUp n (emulate n t))
    | U.inl t => inSumDwn n (S.inl (emulate n t))
    | U.inr t => inSumDwn n (S.inr (emulate n t))
    | U.caseof t₁ t₂ t₃ => S.caseof (caseSumUp n (emulate n t₁)) (emulate n t₂) (emulate n t₃)
    | U.seq t₁ t₂ => S.seq (caseUnitUp n (emulate n t₁)) (emulate n t₂)
  end.

Fixpoint emulate_pctx (n : nat) (t : U.PCtx) : S.PCtx :=
  match t with
    | U.phole => S.phole
    | U.pabs C => S.phole (* inArrDwn n (S.pabs (UVal n) (emulate_pctx n C)) *)
    | U.papp₁ C t₂ => S.papp₁ S.phole (* (caseArrUp n (emulate_pctx n C)) *) (emulate n t₂)
    | U.papp₂ t₁ C => S.papp₂ (caseArrUp n (emulate n t₁)) (emulate_pctx n C)
    | U.pite₁ C₁ t₂ t₃ => S.pite₁ S.phole (* (caseBoolUp n (emulate_pctx n C₁)) *) (emulate n t₂) (emulate n t₃)
    | U.pite₂ t₁ C₂ t₃ => S.pite₂ (caseBoolUp n (emulate n t₁)) (emulate_pctx n C₂) (emulate n t₃)
    | U.pite₃ t₁ t₂ C₃ => S.pite₃ (caseBoolUp n (emulate n t₁)) (emulate n t₂) (emulate_pctx n C₃)
    | U.ppair₁ C₁ t₂ => S.phole (* inProdDwn n (S.ppair₁ (emulate_pctx n C₁) (emulate n t₂)) *)
    | U.ppair₂ t₁ C₂ => S.phole (* inProdDwn n (S.ppair₂ (emulate n t₁) (emulate_pctx n C₂)) *)
    | U.pproj₁ C => S.phole (* S.pproj₁ (caseProdUp n (emulate_pctx n C)) *)
    | U.pproj₂ C => S.phole (* S.pproj₂ (caseProdUp n (emulate_pctx n C)) *)
    | U.pinl C => S.phole (* inSumDwn n (S.pinl (emulate_pctx n C)) *)
    | U.pinr C => S.phole (* inSumDwn n (S.pinr (emulate_pctx n C)) *)
    | U.pcaseof₁ C₁ t₂ t₃ => S.phole (* S.pcaseof₁ (caseSumUp n (emulate_pctx n C₁)) (emulate n t₂) (emulate n t₃) *)
    | U.pcaseof₂ t₁ C₂ t₃ => S.pcaseof₂ (caseSumUp n (emulate n t₁)) (emulate_pctx n C₂) (emulate n t₃)
    | U.pcaseof₃ t₁ t₂ C₃ => S.pcaseof₃ (caseSumUp n (emulate n t₁)) (emulate n t₂) (emulate_pctx n C₃)
    | U.pseq₁ C₁ t₂ => S.phole (* S.seq (caseUnitUp n (emulate_pctx n C₁)) (emulate n t₂) *)
    | U.pseq₂ t₁ C₂ => S.pseq₂ (caseUnitUp n (emulate n t₁)) (emulate_pctx n C₂)
  end.

Fixpoint toUVals n (Γ : Dom) : Env :=
  match Γ with
      0 => S.empty
    | S Γ' => toUVals n Γ' ▻ UVal n
  end.

Lemma toUVals_entry {n Γ i} :
  Γ ∋ i → ⟪ i : UVal n ∈ toUVals n Γ ⟫.
Proof.
  induction 1; simpl; crushTyping.
Qed.

Lemma emulate_T {n Γ t} :
  ⟨ Γ ⊢ t ⟩ →
  ⟪ toUVals n Γ ⊢ emulate n t : UVal n ⟫.
Proof.
  induction 1;
  eauto using stlcOmegaT, toUVals_entry with typing uval_typing.
Qed.

