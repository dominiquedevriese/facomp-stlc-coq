Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcIso.LemmasEvaluation.
(* Require Import StlcIso.LemmasScoping. *)
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecEquivalent.
(* Require Import StlcIso.SpecScoping. *)
Require Import StlcIso.SpecSyntax.
Require Import UValFI.UVal.

Module F.
  Include StlcFix.LemmasEvaluation.
  Include StlcFix.LemmasTyping.
  Include StlcFix.SpecEvaluation.
  Include StlcFix.SpecEquivalent.
  Include StlcFix.SpecSyntax.
  Include StlcFix.SpecTyping.
End F.

Module I.
  Include StlcIso.LemmasEvaluation.
  (* Include StlcIso.LemmasScoping. *)
  Include StlcIso.SpecEvaluation.
  Include StlcIso.SpecEquivalent.
  (* Include StlcIso.SpecScoping. *)
  Include StlcIso.SpecSyntax.
End I.

Inductive Prec : Set :=
| precise
| imprecise.

Inductive PTy : Set :=
| ptarr (τ₁ τ₂ : PTy)
| ptunit
(* | ptbool *)
(* | ptprod (τ₁ τ₂ : PTy) *)
| ptsum (τ₁ τ₂ : PTy)
| pEmulDV (n : nat) (p : Prec) (τ : I.Ty).

Fixpoint repEmul (τ : PTy) : F.Ty :=
  match τ with
    | ptarr τ₁ τ₂ => F.tarr (repEmul τ₁) (repEmul τ₂)
    | ptunit => F.tunit
    (* | ptbool => tbool *)
    (* | ptprod τ₁ τ₂ => tprod (repEmul τ₁) (repEmul τ₂) *)
    | ptsum τ₁ τ₂ => F.tsum (repEmul τ₁) (repEmul τ₂)
    | pEmulDV n p T => UValFI n T
  end.

Fixpoint fxToIs (τ : PTy) : I.Ty :=
  match τ with
    | ptunit => I.tunit
    | ptarr τ₁ τ₂ => I.tarr (fxToIs τ₁) (fxToIs τ₂)
    | ptsum τ₁ τ₂ => I.tsum (fxToIs τ₁) (fxToIs τ₂)
    | pEmulDV n p T => T
  end.

Definition OfTypeStlcFix (τ : PTy) (t : F.Tm) : Prop :=
  F.Value t ∧ (F.Typing F.empty t (repEmul τ) ).

(* Fixpoint OfTypeStlcIso' (τ : PTy) (t : U.UTm) : Prop := *)
(*   match τ with *)
(*     | ptarr τ₁ τ₂ => *)
(*       match t with *)
(*         | U.abs _ => True *)
(*         | _       => False *)
(*       end *)
(*     | ptunit => t = U.unit *)
(*     (* | ptbool => t = U.true ∨ t = U.false *) *)
(*     (* | ptprod τ₁ τ₂ => *) *)
(*     (*   match t with *) *)
(*     (*     | U.pair t₁ t₂ => OfTypeStlcIso' τ₁ t₁ ∧ OfTypeStlcIso' τ₂ t₂ *) *)
(*     (*     | _            => False *) *)
(*     (*   end *) *)
(*     | ptsum τ₁ τ₂ => *)
(*       match t with *)
(*         | U.inl t₁ => OfTypeStlcIso' τ₁ t₁ *)
(*         | U.inr t₂ => OfTypeStlcIso' τ₂ t₂ *)
(*         | _        => False *)
(*       end *)
(*     | pEmulDV n p => U.Value t *)
(*   end. *)
(* Arguments OfTypeStlcIso' !τ !t /. *)

Definition OfTypeStlcIso (τ : PTy) (t : I.Tm) : Prop :=
  I.Value t ∧ I.Typing (I.empty) t (fxToIs τ).

Arguments OfTypeStlcIso !τ !t /.

Definition OfType (τ : PTy) (t₁ : F.Tm) (t₂ : I.Tm) : Prop :=
  OfTypeStlcFix τ t₁ ∧ OfTypeStlcIso τ t₂.

Inductive PEnv : Set :=
| pempty
| pevar (Γ : PEnv) (τ : PTy).

Notation "Γ p▻ T" := (pevar Γ T) (at level 55, left associativity).

Fixpoint pdom (Γ : PEnv) : Dom :=
  match Γ with
    | pempty => 0
    | pevar Γ _ => S (pdom Γ)
  end.

Reserved Notation "⟪  i : T p∈ Γ  ⟫"
  (at level 0, i at level 98, Γ at level 98).
Inductive GetEvarP : PEnv → Ix → PTy → Prop :=
  | GetEvarHere {Γ T} :
      ⟪   O : T p∈ Γ p▻ T  ⟫
  | GetEvarThere {Γ T T' i} :
      ⟪   i : T p∈ Γ      ⟫ →
      ⟪ S i : T p∈ Γ p▻ T' ⟫
where "⟪  i : T p∈ Γ  ⟫" := (GetEvarP Γ i T).

Lemma pdom_works {i T Γ} :
  ⟪ i : T p∈ Γ ⟫ → pdom Γ ∋ i.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma pdom_works_inv {i Γ} :
  pdom Γ ∋ i → ∃ τ, ⟪ i : τ p∈ Γ ⟫.
Proof.
  revert i. induction Γ; intros i.
  - inversion 1.
  - inversion 1.
    + subst. exists τ. constructor.
    + subst. destruct (IHΓ i0 H1) as (τ0 & iinΓ).
      exists τ0. constructor. assumption.
Qed.

Fixpoint repEmulCtx (Γ : PEnv) : F.Env :=
  match Γ with
    | pempty => F.empty
    | pevar Γ τ => F.evar (repEmulCtx Γ) (repEmul τ)
  end.

Lemma repEmulCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  F.GetEvar (repEmulCtx Γ) i (repEmul τ).
Proof.
  induction 1; eauto using F.GetEvar.
Qed.

Fixpoint fxToIsCtx (Γ : PEnv) : I.Env :=
  match Γ with
  | pempty => I.empty
  | pevar Γ τ => I.evar (fxToIsCtx Γ) (fxToIs τ)
  end.

Lemma fxToIsCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  I.GetEvar (fxToIsCtx Γ) i (fxToIs τ).
Proof.
  induction 1; eauto using I.GetEvar.
Qed.

Fixpoint embed (τ : F.Ty) : PTy :=
  match τ with
    | F.tunit => ptunit
    | F.tarr τ₁ τ₂ => ptarr (embed τ₁) (embed τ₂)
    (* | F.tbool => ptbool *)
    (* | F.tprod τ₁ τ₂ => ptprod (embed τ₁) (embed τ₂) *)
    | F.tsum τ₁ τ₂ => ptsum (embed τ₁) (embed τ₂)
  end.

Fixpoint embedCtx (Γ : F.Env) : PEnv :=
  match Γ with
    | F.empty => pempty
    | F.evar Γ τ => pevar (embedCtx Γ) (embed τ)
  end.

Lemma embedCtx_works {Γ i τ} :
  F.GetEvar Γ i τ →
  ⟪ i : embed τ p∈ embedCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvarP.
Qed.

Lemma embedCtx_works_inv {Γ i τ} :
  ⟪ i : τ p∈ embedCtx Γ ⟫ →
  exists τ', τ = embed τ' ∧ (F.GetEvar Γ i τ').
Proof.
  revert i τ. induction Γ; intros i τ' iτ; simpl in *; inversion iτ; subst.
  - exists τ; intuition.
  - destruct (IHΓ _ _ H3) as [τ'' [eq ty]].
    exists τ''; intuition; eauto using GetEvarP.
Qed.
