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
    | [ H: ⟨ _ ⊢ var _         ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ abs _ _       ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ app _ _       ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ unit          ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ true          ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ false         ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ ite _ _ _     ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ pair _ _      ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ proj₁ _       ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ proj₂ _       ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ inl _         ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ inr _         ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ caseof _ _ _  ⟩ |- _ ] => inversion H; clear H
    | [ H: ⟨ _ ⊢ seq _ _       ⟩ |- _ ] => inversion H; clear H
    | [ |- ⟨ _ ⊢ var _        ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ abs _        ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ app _ _      ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ unit         ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ true         ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ false        ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ ite _ _ _    ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ pair _ _     ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ proj₁ _      ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ proj₂ _      ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ inl _        ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ inr _        ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ caseof _ _ _ ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ seq _ _      ⟩ ] => econstructor
    | [ |- context[wsUTm ?γ ?t] ] =>
      change (wsUTm γ t) with ⟨ γ ⊢ t ⟩
    | [ |- ⟨ ⊢ phole : _ → _        ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pabs _ : _ → _        ⟩ ] => econstructor
    | [ |- ⟨ ⊢ papp₁ _ _ : _ → _     ⟩ ] => econstructor
    | [ |- ⟨ ⊢ papp₂ _ _ : _ → _     ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pite₁ _ _ _  : _ → _  ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pite₂ _ _ _  : _ → _  ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pite₃ _ _ _  : _ → _  ⟩ ] => econstructor
    | [ |- ⟨ ⊢ ppair₁ _ _ : _ → _    ⟩ ] => econstructor
    | [ |- ⟨ ⊢ ppair₂ _ _ : _ → _    ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pproj₁ _ : _ → _     ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pproj₂ _ : _ → _     ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pinl _ : _ → _       ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pinr _ : _ → _       ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pcaseof₁ _ _ _ : _ → _⟩ ] => econstructor
    | [ |- ⟨ ⊢ pcaseof₂ _ _ _ : _ → _⟩ ] => econstructor
    | [ |- ⟨ ⊢ pcaseof₃ _ _ _ : _ → _⟩ ] => econstructor
    | [ |- ⟨ ⊢ pseq₁ _ _ : _ → _     ⟩ ] => econstructor
    | [ |- ⟨ ⊢ pseq₂ _ _ : _ → _     ⟩ ] => econstructor
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