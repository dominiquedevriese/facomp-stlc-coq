Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEquivalent.
Require Import Utlc.SpecEquivalent.

Require Import Compiler.Erase.
Require Import Compiler.ProtectConfine.

Require Import LogRel.LemmasPseudoType.

Definition compile (τ : S.Ty) (t : S.Tm) : U.UTm :=
  U.app (protect τ) (erase t).

(* Coq notations seem to be getting confused here... *)
(* Lemma equivalenceReflection {t₁ t₂ τ} : *)
(*   ⟪ S.empty ⊢ t₁ : τ ⟫ → *)
(*   ⟪ S.empty ⊢ t₂ : τ ⟫ → *)
(*   ⟨ 0 ⊢ compile τ t₁ ≃ compile τ t₂ ⟩ → *)
(*   ⟪ S.empty ⊢ t₁ ≃ τ₂ : τ ⟫. *)