Require Export Utlc.SpecSyntax.

Section WellScoping.

  (* Keep this in a section so that the notation for the ws type-class is only
     locally overwritten. *)
  Inductive wsUTm (γ: Dom) : UTm → Prop :=
    | WsWronng            : ⟨ γ ⊢ wrong ⟩
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
Inductive WsPCtx (γ₀: Dom) (γ: Dom) : PCtx → Prop :=
  | WsPAbs {C} :
      ⟨ ⊢ C : γ₀ → S γ ⟩ →
      ⟨ ⊢ pabs C : γ₀ → γ ⟩
  | WsPAppl {C t₂} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ papp₁ C t₂ : γ₀ → γ ⟩
  | WsPAppr {t₁ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ papp₂ t₁ C : γ₀ → γ ⟩
  | WsPIteI {C t₂ t₃} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pite₁ C t₂ t₃ : γ₀  → γ ⟩
  | WsPIteT {t₁ C t₃} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pite₂ t₁ C t₃ : γ₀ → γ ⟩
  | WsPIteE {t₁ t₂ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pite₃ t₁ t₂ C : γ₀ → γ ⟩
  | WsPPair₁ {C t₂} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ ppair₁ C t₂ : γ₀ → γ ⟩
  | WsPPair₂ {t₁ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ ppair₂ t₁ C : γ₀ → γ ⟩
  | WsPProj₁ {C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pproj₁ C : γ₀ → γ ⟩
  | WsPProj₂ {C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pproj₂ C : γ₀ → γ ⟩
  | WsPInl {C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pinl C : γ₀ → γ ⟩
  | WsPInr {C} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ ⊢ pinr C : γ₀ → γ ⟩
  | WsPCaseof₁ {C t₂ t₃} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ S γ ⊢ t₂ ⟩ →
      ⟨ S γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pcaseof₁ C t₂ t₃ : γ₀ → γ ⟩
  | WsPCaseof₂ {t₁ C t₃} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ ⊢ C : γ₀ → S γ ⟩ →
      ⟨ S γ ⊢ t₃ ⟩ →
      ⟨ ⊢ pcaseof₂ t₁ C t₃ : γ₀ → γ ⟩
  | WsPCaseof₃ {t₁ t₂ C} :
      ⟨ γ ⊢ t₁ ⟩ →
      ⟨ S γ ⊢ t₂ ⟩ →
      ⟨ ⊢ C : γ₀ → S γ ⟩ →
      ⟨ ⊢ pcaseof₃ t₁ t₂ C : γ₀ → γ ⟩
  | WsPSeq₁ {C t₂} :
      ⟨ ⊢ C : γ₀ → γ ⟩ →
      ⟨ γ ⊢ t₂ ⟩ →
      ⟨ ⊢ pseq₁ C t₂ : γ₀ → γ ⟩
where "⟨ ⊢ C : γ₀ → γ ⟩" := (WsPCtx γ₀ γ C).
