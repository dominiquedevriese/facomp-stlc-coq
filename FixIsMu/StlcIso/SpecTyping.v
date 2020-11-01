Require Export StlcIso.Inst.
Require Export StlcIso.SpecSyntax.

(** * Typing *)

Reserved Notation "⟪  i : T ∈ Γ  ⟫"
  (at level 0, i at level 98, Γ at level 98).
Inductive GetEvar : Env → Ix → Ty → Prop :=
  | GetEvarHere {Γ T} :
      ⟪   O : T ∈ Γ ▻ T  ⟫
  | GetEvarThere {Γ T T' i} :
      ⟪   i : T ∈ Γ      ⟫ →
      ⟪ S i : T ∈ Γ ▻ T' ⟫
where "⟪  i : T ∈ Γ  ⟫" := (GetEvar Γ i T).

(* Fixpoint subt (T T' : Ty) (i : Ix) {struct T} : Ty := *)
(*   match T with *)
(*   | tarr τ τ' => *)
(*     let A := subt τ T' i in *)
(*     let B := subt τ' T' i in *)
(*     (tarr A B) *)
(*   | tunit => tunit *)
(*   | tsum τ τ' => *)
(*     let A := (⟪ τ : i -> T' ⟫) in *)
(*     let B := (⟪ τ' : i -> T' ⟫) in *)
(*     (tsum A B) *)
(*   end *)
(*  where "⟪ T : i -> S ⟫" := (subt T S i). *)

Inductive ClosedNTy (n : nat) : Ty → Prop :=
    | UnitClosed :
        ClosedNTy n tunit
    | FnClosed {τ τ'} :
        ClosedNTy n τ →
        ClosedNTy n τ' →
        ClosedNTy n (tarr τ τ')
    | ClosedSum {τ τ'} :
        ClosedNTy n τ →
        ClosedNTy n τ' →
        ClosedNTy n (tsum τ τ')
    | ClosedRec {τ} :
        ClosedNTy (S n) τ →
        ClosedNTy n (trec τ)
    | ClosedVar {i} :
        i < n →
        ClosedNTy n (tvar i).

Definition ClosedTy : Ty → Prop := ClosedNTy 0.


Reserved Notation "⟪  Γ ⊢ t : T  ⟫"
  (at level 0, Γ at level 98, t at level 98, T at level 98 ).
Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | WtVar {i T} :
      ⟪ i : T ∈ Γ ⟫ →
      ⟪ Γ ⊢ var i : T ⟫
  | WtAbs {t τ₁ τ₂} :
      ⟪ Γ ▻ τ₁ ⊢ t : τ₂ ⟫ →
      ⟪ Γ ⊢ abs τ₁ t : tarr τ₁ τ₂ ⟫
  | WtApp {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ ⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ Γ ⊢ t₂ : τ₁ ⟫ →
      ⟪ Γ ⊢ app t₁ t₂ : τ₂ ⟫
  | WtUnit :
      ⟪ Γ ⊢ unit : tunit ⟫
  (* | WtTrue : *)
  (*     ⟪ Γ ⊢ true : tbool ⟫ *)
  (* | WtFalse : *)
  (*     ⟪ Γ ⊢ false : tbool ⟫ *)
  (* | WtIte {t₁ t₂ t₃ T} : *)
  (*     ⟪ Γ ⊢ t₁ : tbool ⟫ → *)
  (*     ⟪ Γ ⊢ t₂ : T ⟫ → *)
  (*     ⟪ Γ ⊢ t₃ : T ⟫ → *)
  (*     ⟪ Γ ⊢ ite t₁ t₂ t₃ : T ⟫ *)
  (* | WtPair {t₁ t₂ τ₁ τ₂} : *)
  (*     ⟪ Γ ⊢ t₁ : τ₁ ⟫ → *)
  (*     ⟪ Γ ⊢ t₂ : τ₂ ⟫ → *)
  (*     ⟪ Γ ⊢ pair t₁ t₂ : tprod τ₁ τ₂ ⟫ *)
  (* | WtProj1 {t τ₁ τ₂} : *)
  (*     ⟪ Γ ⊢ t : tprod τ₁ τ₂ ⟫ → *)
  (*     ⟪ Γ ⊢ proj₁ t : τ₁ ⟫ *)
  (* | WtProj2 {t τ₁ τ₂} : *)
  (*     ⟪ Γ ⊢ t : tprod τ₁ τ₂ ⟫ → *)
  (*     ⟪ Γ ⊢ proj₂ t : τ₂ ⟫ *)
  | WtInl {t τ₁ τ₂} :
      ⟪ Γ ⊢ t : τ₁ ⟫ →
      ⟪ Γ ⊢ inl t : tsum τ₁ τ₂ ⟫
  | WtInr {t τ₁ τ₂} :
      ⟪ Γ ⊢ t : τ₂ ⟫ →
      ⟪ Γ ⊢ inr t : tsum τ₁ τ₂ ⟫
  | WtCaseof {t₁ t₂ t₃ τ₁ τ₂ T} :
      ⟪ Γ ⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ ▻ τ₁ ⊢ t₂ : T ⟫ →
      ⟪ Γ ▻ τ₂ ⊢ t₃ : T ⟫ →
      ⟪ Γ ⊢ caseof t₁ t₂ t₃ : T ⟫
  | WtFold {t τ} :
      ⟪ Γ ⊢ t : τ[beta1 (trec τ)] ⟫ →
      ⟪ Γ ⊢ fold_ t : trec τ ⟫
  | WtUnfold {t τ} :
      ⟪ Γ ⊢ t : trec τ ⟫ →
      ⟪ Γ ⊢ unfold_ t : τ[beta1 (trec τ)] ⟫
  (* | WtSeq {t₁ t₂ T} : *)
  (*     ⟪ Γ ⊢ t₁ : tunit ⟫ → *)
  (*     ⟪ Γ ⊢ t₂ : T ⟫ → *)
  (*     ⟪ Γ ⊢ seq t₁ t₂ : T ⟫ *)
  (* | WtFixt {τ₁ τ₂ t} : *)
  (*     ⟪ Γ ⊢ t : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ → *)
  (*     ⟪ Γ ⊢ fixt τ₁ τ₂ t : tarr τ₁ τ₂ ⟫ *)
where "⟪  Γ ⊢ t : T  ⟫" := (Typing Γ t T).

Reserved Notation "⟪ ⊢ C : Γ₀ , τ₀ → Γ , τ ⟫"
  (at level 0, C at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ⊢  C  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").
Inductive PCtxTyping (Γ₀: Env) (τ₀: Ty) : Env → PCtx → Ty → Prop :=
  | WtPHole :
      ⟪ ⊢ phole : Γ₀, τ₀ → Γ₀, τ₀ ⟫
  | WtPAbs {Γ C τ₁ τ₂} :
      ⟪ ⊢ C : Γ₀, τ₀ → Γ ▻ τ₁, τ₂ ⟫ →
      ⟪ ⊢ pabs τ₁ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫
  | WtPAppl {Γ C t₂ τ₁ τ₂} :
      ⟪ ⊢ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫ →
      ⟪ Γ ⊢ t₂ : τ₁ ⟫ →
      ⟪ ⊢ papp₁ C t₂ : Γ₀, τ₀ → Γ, τ₂ ⟫
  | WtPAppr {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ ⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ ⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ ⊢ papp₂ t₁ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  (* | WtPIteI {Γ C t₂ t₃ T} : *)
  (*     ⟪ ⊢ C : Γ₀, τ₀ → Γ , tbool ⟫ → *)
  (*     ⟪ Γ ⊢ t₂ : T ⟫ → *)
  (*     ⟪ Γ ⊢ t₃ : T ⟫ → *)
  (*     ⟪ ⊢ pite₁ C t₂ t₃ : Γ₀ , τ₀ → Γ , T ⟫ *)
  (* | WtPIteT {Γ t₁ C t₃ T} : *)
  (*     ⟪ Γ ⊢ t₁ : tbool ⟫ → *)
  (*     ⟪ ⊢ C : Γ₀ , τ₀ → Γ , T ⟫ → *)
  (*     ⟪ Γ ⊢ t₃ : T ⟫ → *)
  (*     ⟪ ⊢ pite₂ t₁ C t₃ : Γ₀ , τ₀ → Γ , T ⟫ *)
  (* | WtPIteE {Γ t₁ t₂ C T} : *)
  (*     ⟪ Γ ⊢ t₁ : tbool ⟫ → *)
  (*     ⟪ Γ ⊢ t₂ : T ⟫ → *)
  (*     ⟪ ⊢ C : Γ₀ , τ₀ → Γ , T ⟫ → *)
  (*     ⟪ ⊢ pite₃ t₁ t₂ C : Γ₀ , τ₀ → Γ , T ⟫ *)
  (* | WtPPair₁ {Γ C t₂ τ₁ τ₂} : *)
  (*     ⟪ ⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ → *)
  (*     ⟪ Γ ⊢ t₂ : τ₂ ⟫ → *)
  (*     ⟪ ⊢ ppair₁ C t₂ : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ *)
  (* | WtPPair₂ {Γ t₁ C τ₁ τ₂} : *)
  (*     ⟪ Γ ⊢ t₁ : τ₁ ⟫ → *)
  (*     ⟪ ⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ → *)
  (*     ⟪ ⊢ ppair₂ t₁ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ *)
  (* | WtPProj₁ {Γ C τ₁ τ₂} : *)
  (*     ⟪ ⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ → *)
  (*     ⟪ ⊢ pproj₁ C : Γ₀, τ₀ → Γ, τ₁ ⟫ *)
  (* | WtPProj₂ {Γ C τ₁ τ₂} : *)
  (*     ⟪ ⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ → *)
  (*     ⟪ ⊢ pproj₂ C : Γ₀, τ₀ → Γ, τ₂ ⟫ *)
  | WtPInl {Γ C τ₁ τ₂} :
      ⟪ ⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ ⊢ pinl C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | WtPInr {Γ C τ₁ τ₂} :
      ⟪ ⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ ⊢ pinr C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | WtPCaseof₁ {Γ C t₂ t₃ τ₁ τ₂ T} :
      ⟪ ⊢ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫ →
      ⟪ Γ ▻ τ₁ ⊢ t₂ : T ⟫ →
      ⟪ Γ ▻ τ₂ ⊢ t₃ : T ⟫ →
      ⟪ ⊢ pcaseof₁ C t₂ t₃ : Γ₀, τ₀ → Γ, T ⟫
  | WtPCaseof₂ {Γ t₁ C t₃ τ₁ τ₂ T} :
      ⟪ Γ ⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ ⊢ C : Γ₀, τ₀ → Γ ▻ τ₁, T ⟫ →
      ⟪ Γ ▻ τ₂ ⊢ t₃ : T ⟫ →
      ⟪ ⊢ pcaseof₂ t₁ C t₃ : Γ₀, τ₀ → Γ, T ⟫
  | WtPCaseof₃ {Γ t₁ t₂ C τ₁ τ₂ T} :
      ⟪ Γ ⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ ▻ τ₁ ⊢ t₂ : T ⟫ →
      ⟪ ⊢ C : Γ₀, τ₀ → Γ ▻ τ₂, T ⟫ →
      ⟪ ⊢ pcaseof₃ t₁ t₂ C : Γ₀, τ₀ → Γ, T ⟫
  (* | WtPSeq₁ {Γ C t₂ T} : *)
  (*     ⟪ ⊢ C : Γ₀, τ₀ → Γ, tunit ⟫ → *)
  (*     ⟪ Γ ⊢ t₂ : T ⟫ → *)
  (*     ⟪ ⊢ pseq₁ C t₂ : Γ₀, τ₀ → Γ, T ⟫ *)
  (* | WtPFixt {Γ τ₁ τ₂ C} : *)
  (*     ⟪ ⊢ C : Γ₀, τ₀ → Γ, tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ → *)
  (*     ⟪ ⊢ pfixt τ₁ τ₂ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫ *)
where "⟪ ⊢ C : Γ₀ , τ₀ → Γ , τ ⟫" := (PCtxTyping Γ₀ τ₀ Γ C τ).

Lemma pctxtyping_app {Γ₀ t₀ τ₀ Γ C τ} :
  ⟪ Γ₀ ⊢ t₀ : τ₀ ⟫ → ⟪ ⊢ C : Γ₀, τ₀ → Γ , τ ⟫ → ⟪ Γ ⊢ pctx_app t₀ C : τ ⟫.
Proof.
  intros wt₀ wC;
  induction wC; cbn; subst; eauto using Typing.
Qed.

Lemma pctxtyping_cat {Γ₀ τ₀ C₁ Γ₁ τ₁ C₂ Γ₂ τ₂} :
  ⟪ ⊢ C₁ : Γ₀, τ₀ → Γ₁ , τ₁ ⟫ →
  ⟪ ⊢ C₂ : Γ₁, τ₁ → Γ₂ , τ₂ ⟫ →
  ⟪ ⊢ pctx_cat C₁ C₂ : Γ₀, τ₀ → Γ₂ , τ₂ ⟫.
Proof.
  intros wC₁ wC₂.
  induction wC₂; cbn; eauto using PCtxTyping.
Qed.

Definition WtRen (Γ₁ Γ₂: Env) (ξ: Sub Ix) : Prop :=
  ∀ i T, ⟪ i : T ∈ Γ₁ ⟫ → ⟪ (ξ i) : T ∈ Γ₂ ⟫.
Definition WtSub (Γ₁ Γ₂: Env) (ζ: Sub Tm) : Prop :=
  ∀ i T, ⟪ i : T ∈ Γ₁ ⟫ → ⟪ Γ₂ ⊢ (ζ i) : T ⟫.
