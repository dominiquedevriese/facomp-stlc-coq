Require Export LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.PseudoType.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.SpecTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.Inst.
Require Import UVal.UVal.

Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Wf_nat.
Require Import Omega.

Inductive Direction : Set :=
| dir_lt
| dir_gt.

Definition World := nat.
Definition lev : World → nat := fun w => w.

Definition PTRel := PTy → S.Tm → U.UTm → Prop.
Definition PCRel := PTy → S.PCtx → U.PCtx → Prop.

(* Intuitively: observing termination takes a step in addition to the actual evaluation steps *)
Definition Observe (n : nat) (T : nat → Prop) : Prop :=
  match n with
    | 0 => False
    | S n' => T n'
  end.

Lemma lt_le {w w' w''} (fw : w' < w) (fw' : w'' ≤ w') : w'' < w.
Proof.
  unfold lt in *.
  refine (le_trans _ _ _ _ fw).
  refine (le_n_S _ _ fw').
Defined.

Definition prod_rel (R₁ R₂ : S.Tm → U.UTm → Prop) : S.Tm → U.UTm → Prop :=
  fun ts tu =>
    match ts , tu with
      | S.pair ts₁ ts₂ , U.pair tu₁ tu₂ => R₁ ts₁ tu₁ ∧ R₂ ts₂ tu₂
      | _              , _              => False
    end.
Definition sum_rel (R₁ R₂ : S.Tm → U.UTm → Prop) : S.Tm → U.UTm → Prop :=
  fun ts tu =>
    match ts , tu with
      | S.inl ts' , U.inl tu' => R₁ ts' tu'
      | S.inr ts' , U.inr tu' => R₂ ts' tu'
      | _         , _         => False
    end.
Definition arr_rel (R₁ R₂ : S.Tm → U.UTm → Prop) : S.Tm → U.UTm → Prop :=
  fun ts tu =>
    match ts , tu with
      | S.abs τ₁' tsb , U.abs tub =>
        ∀ ts' tu',
          R₁ ts' tu' →
          R₂ (tsb [beta1 ts']) (tub [beta1 tu'])
      | _ , _ => False
    end.

Arguments prod_rel R₁ R₂ !ts !tu.
Arguments sum_rel R₁ R₂ !ts !tu.
Arguments arr_rel R₁ R₂ !ts !tu.

Section LogicalRelation.

  Variable (d: Direction).

  Definition Obs (w : World) (ts : S.Tm) (tu : U.UTm) :=
    match d with
      | dir_lt => Observe (lev w) (S.TerminatingN ts) → U.Terminating tu
      | dir_gt => Observe (lev w) (U.TerminatingN tu) → S.Terminating ts
    end.

  Definition contrel' (w : World) (vr' : ∀ w' : World, w' ≤ w → PTRel) : PCRel :=
   fun τ Cs Cu => ∀ w' (fw : w' ≤ w) ts tu, vr' w' fw τ ts tu → Obs w' (S.pctx_app ts Cs) (U.pctx_app tu Cu).

  Definition termrel' (w : World) (vr' : ∀ w' : World, w' ≤ w → PTRel) : PTRel :=
    fun τ ts tu => ∀ Cs Cu, S.ECtx Cs → U.ECtx Cu → contrel' w vr' τ Cs Cu → Obs w (S.pctx_app ts Cs) (U.pctx_app tu Cu).

  Definition valrel' (w : World) (ind : ∀ w' : World, w' < w → PTRel) : PTRel :=
    fun τ ts tu =>
      OfType τ ts tu ∧
      let latervr : PTRel := fun τ ts tu => ∀ w' (fw : w' < w), ind w' fw τ ts tu in
      let laterlatervr : ∀ w' (fw : w' < w) w'' (fw' : w'' ≤ w'), PTRel := fun w' fw w'' fw' => ind w'' (lt_le fw fw') in
      let vrunit : S.Tm → U.UTm → Prop := fun ts tu => ts = S.unit ∧ tu = U.unit in
      let vrbool : S.Tm → U.UTm → Prop := fun ts tu => (ts = S.true ∧ tu = U.true) ∨ (ts = S.false ∧ tu = U.false) in
      let vrprod : PTy → PTy → S.Tm → U.UTm → Prop :=
          fun τ₁ τ₂ =>
            prod_rel (latervr τ₁) (latervr τ₂) in
      let vrsum : PTy → PTy → S.Tm → U.UTm → Prop :=
          fun τ₁ τ₂ =>
            sum_rel (latervr τ₁) (latervr τ₂) in
      let vrarr : PTy → PTy → S.Tm → U.UTm → Prop :=
          fun τ₁ τ₂ ts tu =>
            ∀ w' (fw : w' < w),
              arr_rel
                (ind w' fw τ₁)
                (termrel' w' (laterlatervr w' fw) τ₂)
                ts tu
      in
      match τ with
        | ptunit => vrunit ts tu
        | ptbool => vrbool ts tu
        | ptprod τ₁ τ₂ => vrprod τ₁ τ₂ ts tu
        | ptsum τ₁ τ₂ => vrsum τ₁ τ₂ ts tu
        | ptarr τ₁ τ₂ => vrarr τ₁ τ₂ ts tu
        | pEmulDV n p => match n with
                           | 0 => ts = S.unit ∧ p = imprecise
                           | S n' => (ts = unkUVal (S n') ∧ p = imprecise) ∨
                                     exists ts',
                                       (ts = inUnit n' ts' ∧ vrunit ts' tu) ∨
                                       (ts = inBool n' ts' ∧ vrbool ts' tu) ∨
                                       (ts = inProd n' ts' ∧ vrprod (pEmulDV n' p) (pEmulDV n' p) ts' tu) ∨
                                       (ts = inSum n' ts' ∧ vrsum (pEmulDV n' p) (pEmulDV n' p) ts' tu) ∨
                                       (ts = inArr n' ts' ∧ vrarr (pEmulDV n' p) (pEmulDV n' p) ts' tu)
                         end
      end.

  Definition valrel (w : World) (τ : PTy)(t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
    Fix lt_wf (fun w => PTRel) valrel' w τ t₁ t₂.

  Lemma valrel_def_funext w (ind₁ ind₂ : ∀ w', w' < w → PTRel) :
    (∀ w' (fw : w' < w), ind₁ w' fw = ind₂ w' fw) →
    valrel' w ind₁ = valrel' w ind₂.
  Proof.
    intros.
    enough (ind₁ = ind₂) as -> by auto.
    extensionality w'.
    extensionality fw.
    trivial.
  Qed.

  Lemma valrel_fixp : ∀ w, valrel w = valrel' w (fun w _ => valrel w).
  Proof.
    refine (Fix_eq lt_wf (fun w => PTRel) valrel' valrel_def_funext).
  Qed.

  Definition contrel (w : World) : PCRel :=
    contrel' w (fun w fw => valrel w).

  Definition termrel (w : World) : PTRel :=
    termrel' w (fun w fw => valrel w).

  Lemma termrel_fixp :
    ∀ w, termrel w = termrel' w (fun w _ => valrel' w (fun w _ => valrel w)).
  Proof.
    unfold termrel.
    intros w.
    f_equal.
    (* Should we avoid functional extensionality? *)
    extensionality w'.
    extensionality fw.
    apply valrel_fixp.
  Qed.

  Definition envrel (w : World) (Γ : PEnv) (γs : Sub S.Tm) (γu : Sub U.UTm) : Prop :=
    ∀ i τ, ⟪ i : τ p∈ Γ ⟫ → valrel w τ (γs i) (γu i).

  Definition OpenLRN (n : nat) (Γ : PEnv) (ts : S.Tm) (tu : U.UTm) (τ : PTy) : Prop :=
    ⟪ repEmulCtx Γ ⊢ ts : repEmul τ ⟫ ∧
    ∀ w, lev w ≤ n → ∀ γs γu, envrel w Γ γs γu → termrel w τ (ts [ γs ]) (tu [ γu ]).

  Definition OpenLR (Γ : PEnv) (ts : S.Tm) (tu : U.UTm) (τ : PTy) : Prop :=
    ∀ n, OpenLRN n Γ ts tu τ.

  Definition OpenLRCtxN (n : nat) (Cs : S.PCtx) (Cu : U.PCtx) (Γ' : PEnv) (τ' : PTy) (Γ : PEnv) (τ : PTy) : Prop :=
    ⟪ ⊢ Cs : repEmulCtx Γ' , repEmul τ' → repEmulCtx Γ , repEmul τ ⟫ ∧
    ∀ ts tu, OpenLRN n Γ' ts tu τ' -> OpenLRN n Γ (S.pctx_app ts Cs) (U.pctx_app tu Cu) τ.

  Definition OpenLRCtx (Cs : S.PCtx) (Cu : U.PCtx) (Γ' : PEnv) (τ' : PTy) (Γ : PEnv) (τ : PTy) : Prop :=
    ⟪ ⊢ Cs : repEmulCtx Γ' , repEmul τ' → repEmulCtx Γ' , repEmul τ ⟫ ∧
    ∀ ts tu, OpenLR Γ' ts tu τ' → OpenLR Γ (S.pctx_app ts Cs) (U.pctx_app tu Cu) τ.

End LogicalRelation.

Arguments termrel d w τ t₁ t₂ : simpl never.
Arguments valrel d w τ t₁ t₂ : simpl never.
Arguments valrel' d w ind !τ !t₁ !t₂ /.

Notation "⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ ⟫" := (OpenLRN d n Γ ts tu τ)
  (at level 0, ts at level 98,
   d at level 98, n at level 98,
   tu at level 98,
   Γ at level 98, τ at level 98,
   format "⟪ Γ ⊩  ts ⟦ d , n ⟧ tu  :  τ  ⟫").

Notation "⟪ Γ ⊩ ts ⟦ d ⟧ tu : τ ⟫" := (OpenLR d Γ ts tu τ)
  (at level 0, ts at level 98,
   d at level 98, tu at level 98,
   Γ at level 98, τ at level 98,
   format "⟪ Γ ⊩  ts ⟦ d ⟧ tu  :  τ  ⟫").

Notation "⟪ ⊩ Cs ⟦ d , n ⟧ Cu : Γ₀ , τ₀ → Γ , τ ⟫" := (OpenLRCtxN d n Cs Cu Γ₀ τ₀ Γ τ)
  (at level 0, Cs at level 98,
   d at level 98, n at level 98,
   Cu at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ⊩  Cs ⟦ d , n ⟧ Cu  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").

Notation "⟪ ⊩ Cs ⟦ d ⟧ Cu : Γ₀ , τ₀ → Γ , τ ⟫" := (OpenLRCtx d Cs Cu Γ₀ τ₀ Γ τ)
  (at level 0, Cs at level 98,
   d at level 98, Cu at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ⊩  Cs ⟦ d ⟧ Cu  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").
