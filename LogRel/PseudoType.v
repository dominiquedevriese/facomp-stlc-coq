Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import UVal.UVal.

Inductive Prec : Set :=
| precise
| imprecise.

Inductive PTy : Set :=
| ptarr (τ₁ τ₂ : PTy)
| ptunit
| ptbool
| ptprod (τ₁ τ₂ : PTy)
| ptsum (τ₁ τ₂ : PTy)
| pEmulDV (n : nat) (p : Prec).

Inductive PEnv : Set :=
| pempty
| pevar (Γ : PEnv) (τ : PTy).

Notation "Γ p▻ T" := (pevar Γ T) (at level 55, left associativity).

Reserved Notation "⟪  i : T p∈ Γ  ⟫"
  (at level 0, i at level 98, Γ at level 98).
Inductive GetEvarP : PEnv → Ix → PTy → Prop :=
  | GetEvarHere {Γ T} :
      ⟪   O : T p∈ Γ p▻ T  ⟫
  | GetEvarThere {Γ T T' i} :
      ⟪   i : T p∈ Γ      ⟫ →
      ⟪ S i : T p∈ Γ p▻ T' ⟫
where "⟪  i : T p∈ Γ  ⟫" := (GetEvarP Γ i T).

Fixpoint repEmul (τ : PTy) : Ty :=
  match τ with
    | ptarr τ₁ τ₂ => tarr (repEmul τ₁) (repEmul τ₂)
    | ptunit => tunit
    | ptbool => tbool
    | ptprod τ₁ τ₂ => tprod (repEmul τ₁) (repEmul τ₂)
    | ptsum τ₁ τ₂ => tsum (repEmul τ₁) (repEmul τ₂)
    | pEmulDV n p => UVal n
  end.

Fixpoint repEmulCtx (Γ : PEnv) : Env :=
  match Γ with
    | pempty => empty
    | pevar Γ τ => evar (repEmulCtx Γ) (repEmul τ)
  end.

Lemma repEmulCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  ⟪ i : repEmul τ ∈ repEmulCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvar. 
Qed.

Fixpoint embed (τ : Ty) : PTy :=
  match τ with
    | tarr τ₁ τ₂ => ptarr (embed τ₁) (embed τ₂)
    | tunit => ptunit
    | tbool => ptbool
    | tprod τ₁ τ₂ => ptprod (embed τ₁) (embed τ₂)
    | tsum τ₁ τ₂ => ptsum (embed τ₁) (embed τ₂)
  end.

Fixpoint embedCtx (Γ : Env) : PEnv :=
  match Γ with
      empty => pempty
    | evar Γ τ => pevar (embedCtx Γ) (embed τ)
  end.

Lemma embedCtx_works {Γ i τ} :
  ⟪ i : τ ∈ Γ ⟫ →
  ⟪ i : embed τ p∈ embedCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvarP. 
Qed.

Lemma embedCtx_works_inv {Γ i τ} :
  ⟪ i : τ p∈ embedCtx Γ ⟫ →
  exists τ', τ = embed τ' ∧ ⟪ i : τ' ∈ Γ ⟫.
Proof.
  revert i τ. induction Γ; intros i τ' iτ; simpl in *; inversion iτ; subst.
  - exists τ; intuition.
  - destruct (IHΓ _ _ H3) as [τ'' [eq ty]].
    exists τ''; intuition; eauto using GetEvarP. 
Qed.

Lemma repEmul_embed_leftinv τ :
  repEmul (embed τ) = τ.
Proof.
  induction τ; simpl; try f_equal; intuition.
Qed.

Lemma repEmulCtx_embedCtx_leftinv Γ :
  repEmulCtx (embedCtx Γ) = Γ.
Proof.
  induction Γ; simpl; try f_equal; eauto using repEmul_embed_leftinv.
Qed.

Lemma getevar_repEmulCtx {i τ Γ} :
  ⟪ i : τ ∈ repEmulCtx Γ ⟫ →
  exists τ', ⟪ i : τ' p∈ Γ ⟫ ∧ τ = repEmul τ'.
Proof.
  revert i. induction Γ as [|Γ IHΓ τ'']; 
  inversion 1; [idtac| destruct (IHΓ _ H4) as [? [? ?]]];
  eauto using GetEvarP.
Qed.