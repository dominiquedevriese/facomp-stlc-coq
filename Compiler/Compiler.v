Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEquivalent.
Require Import Utlc.SpecEquivalent.

Require Import Compiler.Erase.
Require Import Compiler.ProtectConfine.

Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.

Definition compile (τ : S.Ty) (t : S.Tm) : U.UTm :=
  U.app (protect τ) (erase t).

Lemma equivalenceReflection {t₁ t₂ τ} :
  ⟪ S.empty ⊢ t₁ : τ ⟫ →
  ⟪ S.empty ⊢ t₂ : τ ⟫ →
  ⟨ 0 ⊢ compile τ t₁ ≃ compile τ t₂ ⟩ →
  ⟪ S.empty ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  intros ty1 ty2 eq.
  assert (forall d n, ⟪ pempty ⊩ t₁ ⟦ d , n ⟧ compile τ t₁ : embed τ ⟫) by
      (intros d n;
       unfold compile;
       apply protect_transp_open;
       exact (erase_correct ty1)).
  assert (forall d n, ⟪ pempty ⊩ t₂ ⟦ d , n ⟧ compile τ t₂ : embed τ ⟫) by
      (intros d n;
       unfold compile;
       apply protect_transp_open;
       exact (erase_correct ty2)).
  unfold S.PCtxEquivalent.
Admitted.
  (* symmetry? *)
  (* intros C τ' ctxrel. *)
  