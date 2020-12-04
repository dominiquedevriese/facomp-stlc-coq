Require Import StlcIso.CanForm.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.LemmasProgramContext.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     subst*);
  try discriminate;
  eauto with eval.

Ltac progressH :=
  match goal with
    | [ H: ⟪ _ : _ ∈ empty ⟫ |- _         ] => inversion H
    | [ H: _ ∨ _             |- _         ] => destruct H
    | [ H: True              |- _         ] => clear H
    | [ H: False             |- _         ] => inversion H
    | [                      |- False ∨ _ ] => right
    | [                      |- True ∨ _  ] => left; auto
  end;
  stlcCanForm.

Hint Constructors eval : pctx.
Hint Constructors eval₀ : pctx.
Hint Extern 20 (Value _) => cbn : pctx.
Hint Extern 20 (ECtx _) => cbn : pctx.

(* Lemma local_progress {t U} (wt: ⟪ empty ⊢ t : U ⟫) : *)
(*   Value t ∨ *)
(*   ∃ C t₀ t₀', *)
(*     t = pctx_app t₀ C ∧ *)
(*     t₀ -->₀ t₀' ∧ *)
(*     ECtx C. *)
(* Proof. *)
(*   depind wt; *)
(*   repeat *)
(*     (try progressH; cbn in *; destruct_conjs; subst); *)
(*     eauto 20 with pctx; *)
(*     try (exists phole; cbn; eauto 20 with pctx; fail). *)
(* Qed. *)

(* Lemma progress {t U} (wt: ⟪ empty ⊢ t : U ⟫) : *)
(*   Value t ∨ *)
(*   ∃ t', t --> t'. *)
(* Proof. *)
(*   destruct (local_progress wt); destruct_conjs; *)
(*     subst; eauto using eval. *)
(* Qed. *)

Lemma canon_tunit {Γ t} :
  Value t → ⟪ Γ ⊢ t : tunit ⟫ → t = unit.
Proof.
  crush.
  inversion H0.
  rewrite <- H2 in H; induction H.
  rewrite <- H3 in H; induction H.
  reflexivity.
  rewrite <- H4 in H; induction H.
  rewrite <- H2 in H; induction H.
Qed.

Lemma canon_tarr {Γ t τ τ'} :
  Value t → ⟪ Γ ⊢ t : tarr τ τ' ⟫
  → exists t', t = abs τ t'.
  crush.
  inversion H0.
  rewrite <- H2 in H.
  induction H.
  eauto.
  rewrite <- H3 in H.
  induction H.
  rewrite <- H4 in H.
  induction H.
  rewrite <- H2 in H.
  induction H.
Qed.

Lemma canon_tsum {Γ t τ τ'} :
  Value t → ⟪ Γ ⊢ t : tsum τ τ' ⟫
  → exists t', Value t' ∧ (t = inl t' ∨ t = inr t').
Proof.
  intros.
  inversion H0.
  rewrite <- H2 in H.
  induction H.
  rewrite <- H3 in H.
  induction H.
  rewrite <- H2 in H.
  exists t0.
  eauto.
  rewrite <- H2 in H.
  exists t0.
  eauto.
  rewrite <- H4 in H.
  induction H.
  rewrite <- H2 in H; induction H.
Qed.

Lemma canon_trec {Γ t τ} :
  Value t → ⟪ Γ ⊢ t : trec τ ⟫ → exists t', Value t' ∧ (t = fold_ t').
Proof.
  intros.
  inversion H0.
  rewrite <- H2 in H.
  induction H.
  rewrite <- H3 in H.
  induction H.
  rewrite <- H4 in H.
  induction H.
  rewrite <- H2 in H.
  exists t0.
  eauto.
  rewrite <- H2 in H.
  induction H.
Qed.

Lemma context_replacement {Γ C t t' T}
  (hyp: ∀ Γ' T', ⟪ Γ' ⊢ t : T' ⟫ → ⟪ Γ' ⊢ t' : T' ⟫) :
    ⟪ Γ ⊢ pctx_app t C : T ⟫ →
    ⟪ Γ ⊢ pctx_app t' C : T ⟫.
Proof.
  intro wt; depind wt; induction C;
    crush; eauto using Typing.
Qed.

Lemma preservation₀ {t t'} (r : t -->₀ t') :
  ∀ {Γ τ}, ⟪ Γ ⊢ t : τ ⟫ → ⟪ Γ ⊢ t' : τ ⟫.
Proof.
  induction r;
    eauto using context_replacement;
    crushTyping.
Qed.

Lemma preservation {t t'} (r: t --> t') :
  ∀ {Γ τ}, ⟪ Γ ⊢ t : τ ⟫ → ⟪ Γ ⊢ t' : τ ⟫.
Proof.
  induction r.
  eauto using context_replacement, preservation₀.
Qed.

Lemma termination_value {t τ} (wt: ⟪ empty ⊢ t : τ ⟫) :
  t⇓ → ∃ t', t -->* t' ∧ Value t'.
Proof.
  destruct 1; crush.
Qed.
