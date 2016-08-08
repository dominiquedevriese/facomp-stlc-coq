Require Export Utlc.SpecScoping.
Require Import Db.Lemmas.

Lemma ws_pctx_app {γ₀ t₀ γ C} :
  ⟨ γ₀ ⊢ t₀ ⟩ → ⟨ ⊢ C : γ₀ → γ ⟩ → ⟨ γ ⊢ pctx_app t₀ C ⟩.
Proof.
  intros wt₀ wC;
  induction wC; constructor; eauto using wsUTm.
Qed.

Lemma ws_pctx_cat {γ₀ C₁ γ₁ C₂ γ₂} :
  ⟨ ⊢ C₁ : γ₀ → γ₁ ⟩ →
  ⟨ ⊢ C₂ : γ₁ → γ₂ ⟩ →
  ⟨ ⊢ pctx_cat C₁ C₂ : γ₀ → γ₂ ⟩.
Proof.
  intros wC₁ wC₂.
  induction wC₂; cbn; eauto using WsPCtx.
Qed.

(* Connect the well-scoping of program contexts with the
   binding depth of the hole. *)
Lemma ws_pctx_depth {γ₀ γ C} (wC: ⟨ ⊢ C : γ₀ → γ ⟩) :
  γ₀ = γ ∪ depthPCtx C.
Proof.
  induction wC; cbn; subst;
    rewrite ?dunion_assoc; cbn; congruence.
Qed.

(* Similar to the above for 'depthlPctx'. Because of the
   reversed order, the statement involves a foldl-based
   union.
*)
Lemma ws_pctx_depthl {γ₀ γ C} (wC: ⟨ ⊢ C : γ₀ → γ ⟩) :
  γ₀ = foldlDom S (depthlPCtx C) γ.
Proof. induction wC; cbn; congruence. Qed.
