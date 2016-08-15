Require Export LogRel.PseudoType.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.SpecTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.Inst.
Require Import UVal.UVal.
Require Import Coq.Program.Basics.


Require Import Coq.Arith.Wf_nat.
Require Import Omega.

Module S.
   Include Stlc.SpecSyntax.
   Include Stlc.SpecEvaluation.
End S.

Module U.
   Include Utlc.SpecSyntax.
   Include Utlc.SpecEvaluation.
End U.

Definition OfTypeStlc (τ : PTy) (t : S.Tm) : Prop :=
  S.Value t ∧ ⟪ empty ⊢ t : repEmul τ ⟫.

Fixpoint OfTypeUtlc (τ : PTy) (t : U.UTm) : Prop :=
  match τ with
    | ptarr τ₁ τ₂ => exists t', t = abs t'
    | ptunit => t = U.unit
    | ptbool => t = U.true ∨ t = U.false
    | ptprod τ₁ τ₂ => exists t₁ t₂, t = U.pair t₁ t₂ ∧ OfTypeUtlc τ₁ t₁ ∧ OfTypeUtlc τ₂ t₂
    | ptsum τ₁ τ₂ => (exists t₁, t = U.inl t₁ ∧ OfTypeUtlc τ₁ t₁) ∨ (exists t₂, t = U.inr t₂ ∧ OfTypeUtlc τ₂ t₂)
    | pEmulDV n p => Value t
  end.

Definition OfType (τ : PTy) (t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  OfTypeStlc τ t₁ ∧ OfTypeUtlc τ t₂.

Inductive Direction : Set :=
| dir_lt
| dir_gt.

Definition World := nat.
Definition lev : World → nat := fun w => w.

Definition PTRel := PTy -> S.Tm -> U.UTm -> Prop.
Definition PCRel := PTy -> S.PCtx -> U.PCtx -> Prop.

Definition Obs (d : Direction) (w : World) (ts : S.Tm) (tu : U.UTm) :=
  match d with
    | dir_lt => S.TerminatingN ts (lev w) → U.Terminating tu
    | dir_gt => U.TerminatingN tu (lev w) → S.Terminating ts
  end.

Definition contrel'
           (d : Direction) (w : World) (vr' : forall w' : World, w' ≤ w -> PTRel) : PCRel :=
 fun τ Cs Cu => forall w' (fw : w' ≤ w) ts tu, vr' w' fw τ ts tu -> Obs d w' (S.pctx_app ts Cs) (U.pctx_app tu Cu).

Definition termrel'
           (d : Direction) (w : World) (vr' : forall w' : World, w' ≤ w -> PTRel) : PTRel :=
  fun τ ts tu => forall Cs Cu, S.ECtx Cs → U.ECtx Cu → contrel' d w vr' τ Cs Cu -> Obs d w (S.pctx_app ts Cs) (U.pctx_app tu Cu).

Lemma lt_le {w w' w''} (fw : w' < w) (fw' : w'' ≤ w') : w'' < w.
Proof.
  omega.
Defined.

Definition prod_rel (R₁ R₂ : S.Tm -> U.UTm -> Prop) : S.Tm -> U.UTm -> Prop :=
  fun ts tu => 
    exists ts₁ ts₂ tu₁ tu₂,
      ts = S.pair ts₁ ts₂ ∧ tu = U.pair tu₁ tu₂ ∧
      R₁ ts₁ tu₁ ∧ R₂ ts₂ tu₂.
Definition sum_rel (R₁ R₂ : S.Tm -> U.UTm -> Prop) : S.Tm -> U.UTm -> Prop :=
  fun ts tu => 
    (exists ts' tu', ts = S.inl ts' ∧ tu = U.inl tu' ∧ R₁ ts' tu') ∨
    (exists ts' tu', ts = S.inr ts' ∧ tu = U.inr tu' ∧ R₂ ts' tu').

Definition valrel' 
           (d : Direction) (w : World) (ind : forall w' : World, w' < w -> PTRel) : PTRel := 
  fun τ ts tu =>
    OfType τ ts tu ∧
    let latervr : PTRel := fun τ ts tu => forall w' (fw : w' < w), ind w' fw τ ts tu in 
    let laterlatervr : forall w' (fw : w' < w) w'' (fw' : w'' ≤ w'), PTRel := fun w' fw w'' fw' => ind w'' (lt_le fw fw') in 
    let vrunit : S.Tm -> U.UTm -> Prop := fun ts tu => ts = S.unit ∧ tu = U.unit in
    let vrbool : S.Tm -> U.UTm -> Prop := fun ts tu => (ts = S.true ∧ tu = U.true) ∨ (ts = S.false ∧ tu = U.false) in
    let vrprod : PTy -> PTy -> S.Tm -> U.UTm -> Prop := 
        fun τ₁ τ₂ ts tu => 
          prod_rel (latervr τ₁) (latervr τ₂) ts tu in
    let vrsum : PTy -> PTy -> S.Tm -> U.UTm -> Prop := 
        fun τ₁ τ₂ ts tu => 
          sum_rel (latervr τ₁) (latervr τ₂) ts tu in
    let vrarr : PTy -> PTy -> S.Tm -> U.UTm -> Prop := 
        fun τ₁ τ₂ ts tu => 
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
      | pEmulDV n p => match n with
                         | 0 => ts = S.unit ∧ p = imprecise
                         | S n' => (ts = unkUVal (S n') ∧ p = imprecise) ∨
                                   (exists ts', ts = inUnit n ts' ∧ vrunit ts' tu) ∨
                                   (exists ts', ts = inBool n ts' ∧ vrbool ts' tu) ∨
                                   (exists ts', ts = inProd n ts' ∧ vrprod (pEmulDV n' p) (pEmulDV n' p) ts' tu) ∨
                                   (exists ts', ts = inSum n ts' ∧ vrsum (pEmulDV n' p) (pEmulDV n' p) ts' tu) ∨
                                   (exists ts', ts = inArr n ts' ∧ vrarr (pEmulDV n' p) (pEmulDV n' p) ts' tu)
                       end
    end.

Definition valrel (d : Direction) (w : World) (τ : PTy)(t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  Fix (well_founded_ltof World (fun w => w))
                  (fun w => PTRel)
                  (valrel' d) w τ t₁ t₂.

Lemma valrel_def_funext {d} :
  forall w (ind₁ ind₂ : forall w', w' < w → PTRel),
  (forall w' (fw : w' < w), ind₁ w' fw = ind₂ w' fw) →
  valrel' d w ind₁ = valrel' d w ind₂.
Proof.
  intros ind₁ ind₂ hyp.
  unfold valrel'.
  (* Should we simply assume functional extensionality here? *)
Admitted.

Lemma valrel_fixp {d} :
  forall w, valrel d w = valrel' d w (fun w _ => valrel d w).
Proof.
  unfold valrel. 
  Check Fix_eq.
  refine (Fix_eq (well_founded_ltof World (fun w => w)) (fun w => PTRel)
                  (valrel' d) valrel_def_funext).
Qed.

Definition contrel
           (d : Direction) (w : World) : PCRel :=
  contrel' d w (fun w fw => valrel d w).

Definition termrel
           (d : Direction) (w : World) : PTRel :=
  termrel' d w (fun w fw => valrel d w).

(* Lemma valrel_ptarr {d w τ₁ τ₂ tsb tub} :  *)
(*   OfType (ptarr τ₁ τ₂) (S.abs (repEmul τ₁) tsb) (U.abs tub) → *)
(*   (forall w' (fw : w' < w) ts' tu', *)
(*      valrel d w' τ₁ ts' tu' → *)
(*      termrel d w' τ₂ (tsb [beta1 ts']) (tub [beta1 tu'])) →  *)
(*   valrel d w (ptarr τ₁ τ₂) (S.abs (repEmul τ₁) tsb) (U.abs tub). *)
(* Proof. *)
(*   intros ot hyp. *)
(*   rewrite -> valrel_fixp. *)
(*   unfold valrel'. *)
(*   split; try assumption. *)
(*   exists tsb. exists tub. *)
(*   repeat split; auto. *)
(* Qed. *)

Definition envrel (d : Direction) (w : World) (Γ : PEnv) (γs : Sub S.Tm) (γu : Sub U.UTm) : Prop :=
  forall i τ, ⟪ i : τ p∈ Γ ⟫ → valrel d w τ (γs i) (γu i).

Definition OpenLRN (d : Direction) (n : nat) (Γ : PEnv) (ts : S.Tm) (tu : U.UTm) (τ : PTy) : Prop :=
  ⟪ repEmulCtx Γ ⊢ ts : repEmul τ ⟫ ∧
  forall w, lev w ≤ n -> forall γs γu, envrel d w Γ γs γu -> termrel d w τ (ts [ γs ]) (tu [ γu ]).

Notation "⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ ⟫" := (OpenLRN d n Γ ts tu τ)
  (at level 0, ts at level 98, 
   d at level 98, n at level 98,
   tu at level 98,
   Γ at level 98, τ at level 98,
   format "⟪ Γ ⊩  ts ⟦ d , n ⟧ tu  :  τ  ⟫").

Definition OpenLR (d : Direction) (Γ : PEnv) (ts : S.Tm) (tu : U.UTm) (τ : PTy) : Prop :=
  forall n, OpenLRN d n Γ ts tu τ.

Notation "⟪ Γ ⊩ ts ⟦ d ⟧ tu : τ ⟫" := (OpenLR d Γ ts tu τ)
  (at level 0, ts at level 98, 
   d at level 98, tu at level 98,
   Γ at level 98, τ at level 98,
   format "⟪ Γ ⊩  ts ⟦ d ⟧ tu  :  τ  ⟫").

Definition OpenLRCtx (d : Direction) (Cs : S.PCtx) (Cu : U.PCtx) (Γ' : PEnv) (τ' : PTy) (Γ : PEnv) (τ : PTy) : Prop :=
  ⟪ ⊢ Cs : repEmulCtx Γ' , repEmul τ' → repEmulCtx Γ' , repEmul τ ⟫ ∧
  forall ts tu, OpenLR d Γ' ts tu τ' -> OpenLR d Γ (S.pctx_app ts Cs) (U.pctx_app tu Cu) τ.

Notation "⟪ ⊩ Cs ⟦ d ⟧ Cu : Γ₀ , τ₀ → Γ , τ ⟫" := (OpenLRCtx d Cs Cu Γ₀ τ₀ Γ τ)
  (at level 0, Cs at level 98, 
   d at level 98, Cu at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ⊩  Cs ⟦ d ⟧ Cu  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").