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

(* For some reason, seemingly related to type classes, the below doesn't work if I use the ⟨ _ ⊢ _ ⟩ notation rather than the standard notation. Not yet sure if the inversion stuff for hypotheses works... *)
Ltac crushScopingMatchH :=
  match goal with
    | H: ⟨ _ ⊢ var _         ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ abs _ _       ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ app _ _       ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ unit          ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ true          ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ false         ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ ite _ _ _     ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ pair _ _      ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ proj₁ _       ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ proj₂ _       ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ inl _         ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ inr _         ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ caseof _ _ _  ⟩ |- _ => inversion H; clear H
    | H: ⟨ _ ⊢ seq _ _       ⟩ |- _ => inversion H; clear H
    |  |- wsUTm _ (var _)  => econstructor
    |  |- wsUTm _ (abs _)  => econstructor
    |  |- wsUTm _ (app _ _)  => econstructor
    |  |- wsUTm _ unit  => econstructor
    |  |- wsUTm _ true  => econstructor
    |  |- wsUTm _ false  => econstructor
    |  |- wsUTm _ (ite _ _ _)  => econstructor
    |  |- wsUTm _ (pair _ _)  => econstructor
    |  |- wsUTm _ (proj₁ _)  => econstructor
    |  |- wsUTm _ (proj₂ _)  => econstructor
    |  |- wsUTm _ (inl _)  => econstructor
    |  |- wsUTm _ (inr _)  => econstructor
    |  |- wsUTm _ (caseof _ _ _)  => econstructor
    |  |- wsUTm _ (seq _ _)  => econstructor
  end.

Ltac crushUtlcScoping :=
  intros;
  repeat
    (cbn in *;
     repeat crushRewriteH;
     repeat crushDbMatchH;
     repeat crushUtlcSyntaxMatchH;
     repeat crushScopingMatchH;
     (* try discriminate; *)
     eauto with ws
    ).
