Require Export Utlc.SpecSyntax.

Section WellScoping.

  (* Keep this in a section so that the notation for the ws type-class is only
     locally overwritten. *)
  Inductive wsUTm (γ: Dom) : UTm → Prop :=
    | WsWrong            : ⟨ γ ⊢ wrong ⟩
    | WsVar {i}           : γ ∋ i → ⟨ γ ⊢ var i ⟩
    | WsAbs {t}           : ⟨ S γ ⊢ t ⟩ → ⟨ γ ⊢ abs t ⟩
    | WsApp {t₁ t₂}       : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ app t₁ t₂ ⟩
    | WsUnit              : ⟨ γ ⊢ unit ⟩
    | WsTrue              : ⟨ γ ⊢ true ⟩
    | WsFalse             : ⟨ γ ⊢ false ⟩
    | WsIte {t₁ t₂ t₃}    : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ →
                            ⟨ γ ⊢ t₃ ⟩ → ⟨ γ ⊢ ite t₁ t₂ t₃ ⟩
    | WsProj1 {t}         : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ proj₁ t ⟩
    | WsProj2 {t}         : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ proj₂ t ⟩
    | WsPair {t₁ t₂}      : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ pair t₁ t₂ ⟩
    | WsInj₁ {t}          : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ inl t ⟩
    | WsInj₂ {t}          : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ inr t ⟩
    | WsCaseof {t₁ t₂ t₃} : ⟨ γ ⊢ t₁ ⟩ → ⟨ S γ ⊢ t₂ ⟩ →
                            ⟨ S γ ⊢ t₃ ⟩ → ⟨ γ ⊢ caseof t₁ t₂ t₃ ⟩
    | WsSeq {t₁ t₂}       : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ seq t₁ t₂ ⟩
  where "⟨  γ ⊢ t  ⟩" := (wsUTm γ t).

End WellScoping.
Instance WsUTm : Ws UTm := wsUTm.

(* γ₀ denotes the scope at the hole *)
Reserved Notation "⟨ ⊢ C : γ₀ → γ ⟩"
  (at level 0, C at level 98, γ₀ at level 98, γ at level 98,
   format "⟨  ⊢  C  :  γ₀  →  γ  ⟩").
Inductive WsPCtx (γ₀: Dom) : Dom → PCtx → Prop :=
  | WsPHole :
      ⟨ ⊢ phole : γ₀ → γ₀ ⟩
  | WsPAbs {γ C} :
      ⟨ ⊢ C : γ₀ → S γ ⟩ →
      ⟨ ⊢ pabs C : γ₀ → γ ⟩
  | WsPAppl {γ C t₂} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ papp₁ C t₂ : γ₀ → γ ⟩
  | WsPAppr {γ t₁ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ papp₂ t₁ C : γ₀ → γ ⟩
  | WsPIteI {γ C t₂ t₃} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pite₁ C t₂ t₃ : γ₀  → γ ⟩
  | WsPIteT {γ t₁ C t₃} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pite₂ t₁ C t₃ : γ₀ → γ ⟩
  | WsPIteE {γ t₁ t₂ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pite₃ t₁ t₂ C : γ₀ → γ ⟩
  | WsPPair₁ {γ C t₂} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ ppair₁ C t₂ : γ₀ → γ ⟩
  | WsPPair₂ {γ t₁ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ ppair₂ t₁ C : γ₀ → γ ⟩
  | WsPProj₁ {γ C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pproj₁ C : γ₀ → γ ⟩
  | WsPProj₂ {γ C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pproj₂ C : γ₀ → γ ⟩
  | WsPInl {γ C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pinl C : γ₀ → γ ⟩
  | WsPInr {γ C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pinr C : γ₀ → γ ⟩
  | WsPCaseof₁ {γ C t₂ t₃} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ S γ ⊢ t₂ ⟩ →
      ⟨ S γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pcaseof₁ C t₂ t₃ : γ₀ → γ ⟩
  | WsPCaseof₂ {γ t₁ C t₃} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → S γ ⟩ →
      ⟨ S γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pcaseof₂ t₁ C t₃ : γ₀ → γ ⟩
  | WsPCaseof₃ {γ t₁ t₂ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ S γ ⊢ t₂ ⟩ →
      ⟨ ⊢ C : γ₀ → S γ ⟩ →
      ⟨ ⊢ pcaseof₃ t₁ t₂ C : γ₀ → γ ⟩
  | WsPSeq₁ {γ C t₂} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ pseq₁ C t₂ : γ₀ → γ ⟩
where "⟨ ⊢ C : γ₀ → γ ⟩" := (WsPCtx γ₀ γ C).

Ltac crushUtlcScopingMatchH :=
  match goal with
    | [ H: context[wsUTm ?γ ?t]  |- _ ] =>
      change (wsUTm γ t) with ⟨ γ ⊢ t ⟩ in H
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

    | [ |- context[wsUTm ?γ ?t] ] =>
      change (wsUTm γ t) with ⟨ γ ⊢ t ⟩
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
