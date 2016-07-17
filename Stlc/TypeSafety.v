Require Import Stlc.SpecEvaluation.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasProgramContext.

Lemma can_form_tarr {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tarr τ₁ τ₂ ⟫) :
    ∃ t₂, t = abs τ₁ t₂.
Proof. depind wt; try contradiction; eauto. Qed.

(* Lemma can_form_tunit {Γ t} *)
(*   (v: Value t) (wt: ⟪ Γ ⊢ t : tunit ⟫) : *)
(*     t = unit. *)
(* Proof. depind wt; try contradiction; eauto. Qed. *)

Lemma can_form_tbool {Γ t}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tbool ⟫) :
    t = true ∨ t = false.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tprod {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tprod τ₁ τ₂ ⟫) :
    ∃ t₁ t₂, t = pair t₁ t₂.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tsum {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tsum τ₁ τ₂ ⟫) :
    (∃ t₁, t = inl t₁) ∨ (∃ t₂, t = inr t₂).
Proof. depind wt; try contradiction; eauto. Qed.

Ltac progressH :=
  match goal with
    | [ H: ⟪ _ : _ ∈ empty ⟫ |- _         ] => inversion H
    | [ H: _ ∨ _             |- _         ] => destruct H
    | [ H: True              |- _         ] => clear H
    | [ H: False             |- _         ] => inversion H
    | [                      |- False ∨ _ ] => right
    | [                      |- True ∨ _  ] => left; auto
    | [ wt: ⟪ _ ⊢ ?t : tarr _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tarr vt wt); clear wt
    | [ wt: ⟪ _ ⊢ ?t : tbool ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tbool vt wt); clear wt
    | [ wt: ⟪ _ ⊢ ?t : tprod _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tprod vt wt); clear wt
    | [ wt: ⟪ _ ⊢ ?t : tsum _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tsum vt wt); clear wt
  end.

Hint Constructors eval : pctx.
Hint Extern 20 (Value _) => cbn : pctx.
Hint Extern 20 (ECtx _) => cbn : pctx.

Lemma local_progress {t U} (wt: ⟪ empty ⊢ t : U ⟫) :
  Value t ∨
  ∃ C t₀ t₀',
    t = pctx_app t₀ C ∧
    t₀ --> t₀' ∧
    ECtx C.
Proof.
  depind wt;
  repeat
    (try progressH; cbn in *; destruct_conjs; subst);
    eauto 20 with pctx;
    try (exists phole; cbn; eauto 20 with pctx; fail).
Qed.

Lemma progress {t U} (wt: ⟪ empty ⊢ t : U ⟫) :
  Value t ∨
  ∃ t', t --> t'.
Proof.
  destruct (local_progress wt); destruct_conjs;
    subst; eauto using eval.
Qed.

Lemma context_replacement {Γ C t t' T}
  (hyp: ∀ Γ' T', ⟪ Γ' ⊢ t : T' ⟫ → ⟪ Γ' ⊢ t' : T' ⟫) :
    ⟪ Γ ⊢ pctx_app t C : T ⟫ →
    ⟪ Γ ⊢ pctx_app t' C : T ⟫.
Proof.
  intro wt; depind wt; induction C; cbn in *; subst;
    try discriminate; try (inversion x; subst);
    eauto using Typing.
Qed.

Lemma preservation {t t'} (r: t --> t') :
  ∀ {Γ τ}, ⟪ Γ ⊢ t : τ ⟫ → ⟪ Γ ⊢ t' : τ ⟫.
Proof.
  induction r;
    eauto using context_replacement;
    crushTyping.
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)
