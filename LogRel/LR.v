Require Export LogRel.PseudoType.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.SpecTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.Inst.
Require Import UVal.UVal.


Require Import Coq.Arith.Wf_nat.
Require Import Omega.

Module S := Stlc.SpecSyntax.
Module SE := Stlc.SpecEvaluation.
Module U := Utlc.SpecSyntax.
Module UE := Utlc.SpecEvaluation.

Definition OfTypeStlc (τ : PTy) (t : S.Tm) : Prop :=
  ⟪ empty ⊢ t : repEmul τ ⟫.

Fixpoint OfTypeUtlc (τ : PTy) (t : U.UTm) : Prop :=
  match τ with
    | ptarr τ₁ τ₂ => exists t', t = abs t'
    | ptunit => t = U.unit
    | ptbool => t = U.true ∨ t = U.false
    | ptprod τ₁ τ₂ => exists t₁ t₂, t = U.pair t₁ t₂ ∧ OfTypeUtlc τ₁ t₁ ∧ OfTypeUtlc τ₂ t₂
    | ptsum τ₁ τ₂ => (exists t₁, t = U.inl t₁ ∧ OfTypeUtlc τ₁ t₁) ∨ (exists t₂, t = U.inr t₂ ∧ OfTypeUtlc τ₂ t₂)
    | pEmulDV n p => True
  end.

Definition OfType (τ : PTy) (t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  OfTypeStlc τ t₁ ∧ OfTypeUtlc τ t₂.

Inductive Direction : Set :=
| dir_lt
| dir_gt.

Definition World := nat.

Definition PTRel := PTy -> S.Tm -> U.UTm -> Prop.
Definition PCRel := PTy -> S.PCtx -> U.PCtx -> Prop.

Definition Obs (d : Direction) (w : World) (ts : S.Tm) (tu : U.UTm) :=
  match d with
    | dir_lt => SE.TerminatingN ts w → UE.Terminating tu
    | dir_gt => UE.TerminatingN tu w → SE.Terminating ts
  end. 

Definition contrel'
           (d : Direction) (w : World) (vr' : forall w' : World, w' ≤ w -> PTRel) : PCRel :=
 fun τ Cs Cu => forall w' (fw : w' ≤ w) ts tu, vr' w' fw τ ts tu -> Obs d w' (S.pctx_app ts Cs) (U.pctx_app tu Cu).

Definition termrel'
           (d : Direction) (w : World) (vr' : forall w' : World, w' ≤ w -> PTRel) : PTRel :=
  fun τ ts tu => forall w' (fw : w' ≤ w) Cs Cu, contrel' d w vr' τ Cs Cu -> Obs d w' (S.pctx_app ts Cs) (U.pctx_app tu Cu).

Lemma lt_le {w w' w''} (fw : w' < w) (fw' : w'' ≤ w') : w'' < w.
Proof.
  omega.
Defined.

Definition valrel'' 
           (d : Direction) (w : World) (ind : forall w' : World, w' < w -> PTRel) : PTRel := 
  fun τ ts tu =>
  let latervr : PTRel := fun τ ts tu => forall w' (fw : w' < w), ind w' fw τ ts tu in 
  let laterlatervr : forall w' (fw : w' < w) w'' (fw' : w'' ≤ w'), PTRel := fun w' fw w'' fw' => ind w'' (lt_le fw fw') in 
  let vrunit : S.Tm -> U.UTm -> Prop := fun ts tu => ts = S.unit ∧ tu = U.unit in
  let vrbool : S.Tm -> U.UTm -> Prop := fun ts tu => (ts = S.true ∧ tu = U.true) ∨ (ts = S.false ∧ tu = U.false) in
  let vrprod : PTy -> PTy -> S.Tm -> U.UTm -> Prop := 
      fun τ₁ τ₂ ts tu => 
        OfType (ptprod τ₁ τ₂) ts tu ∧
        exists ts₁ ts₂ tu₁ tu₂, ts = S.pair ts₁ ts₂ ∧ tu = U.pair tu₁ tu₂ ∧
                                latervr τ₁ ts₁ tu₁ ∧ latervr τ₂ ts₂ tu₂ in
  let vrsum : PTy -> PTy -> S.Tm -> U.UTm -> Prop := 
      fun τ₁ τ₂ ts tu => 
        OfType (ptsum τ₁ τ₂) ts tu ∧
        (exists ts' tu', ts = S.inl ts' ∧ tu = U.inl tu' ∧ latervr τ₁ ts' tu') ∨
        (exists ts' tu', ts = S.inr ts' ∧ tu = U.inr tu' ∧ latervr τ₂ ts' tu') in
  let vrarr : PTy -> PTy -> S.Tm -> U.UTm -> Prop := 
      fun τ₁ τ₂ ts tu => 
        OfType (ptarr τ₁ τ₂) ts tu ∧ 
        exists tsb tub, ts = S.abs (repEmul τ₁) tsb ∧ tu = U.abs tub ∧
                        forall w' (fw : w' < w) ts' tu',
                          ind w' fw τ₁ ts' tu' ->
                          termrel' d w' (laterlatervr w' fw) τ₂ (tsb [beta1 ts']) (tub [beta1 tu']) in
  match τ with
    | ptunit => vrunit ts tu
    | ptbool => vrbool ts tu
    | ptprod τ₁ τ₂ => vrprod τ₁ τ₂ ts tu
    | ptsum τ₁ τ₂ => vrsum τ₁ τ₂ ts tu
    | ptarr τ₁ τ₂ => vrarr τ₁ τ₂ ts tu
    | pEmulDV n p => OfType (pEmulDV n p) ts tu ∧ 
                     match n with
                       | 0 => ts = S.unit ∧ p = imprecise
                       | S n' => (ts = unkUVal (S n') ∧ p = imprecise) ∨
                                 (exists ts', ts = inUnit n ts' ∧ vrunit ts' tu) ∨
                                 (exists ts', ts = inBool n ts' ∧ vrbool ts' tu) ∨
                                 (exists ts', ts = inProd n ts' ∧ vrprod (pEmulDV n' p) (pEmulDV n' p) ts' tu) ∨
                                 (exists ts', ts = inSum n ts' ∧ vrsum (pEmulDV n' p) (pEmulDV n' p) ts' tu) ∨
                                 (exists ts', ts = inArr n ts' ∧ vrarr (pEmulDV n' p) (pEmulDV n' p) ts' tu)
                     end
  end.

Definition valrel' (d : Direction) (w : World) (τ : PTy)(t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  well_founded_induction_type (well_founded_ltof World (fun w => w))
                  (fun w => forall (τ : PTy) (t₁ : S.Tm) (t₂ : U.UTm), Prop)
                  (valrel'' d) w τ t₁ t₂.

Definition valrel (d : Direction) (τ : PTy) (w : World) (t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  valrel' d w τ t₁ t₂.
  