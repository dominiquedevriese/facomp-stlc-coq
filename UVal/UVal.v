Require Import Stlc.SpecEvaluation.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.

Fixpoint UVal (n : nat) : Ty :=
  match n with
    | 0 => tunit
    | S n => tunit ⊎ tunit ⊎ tbool ⊎ (UVal n × UVal n) ⊎ (UVal n ⇒ UVal n) ⊎ (UVal n ⊎ UVal n)
  end.

Fixpoint unkUVal (n : nat) : Tm :=
  match n with
    | 0 => unit
    | S n => inl unit
  end.

Lemma unkUValT {Γ n} : ⟪ Γ ⊢ unkUVal n : UVal n ⟫.
Proof.
  induction n; eauto using Typing.
Qed.

Definition inUnit (n : nat) (t : Tm) := inr (inl t).

Lemma inUnitT {Γ n t} : ⟪ Γ ⊢ t : tunit ⟫ → ⟪ Γ ⊢ inUnit n t : UVal (S n) ⟫.
Proof.
  intros tt.
  unfold inUnit. crushTyping.
Qed.

Definition inBool (n : nat) (t : Tm): Tm := inr (inr (inl t)).

Lemma inBoolT {Γ n t} : ⟪ Γ ⊢ t : tbool ⟫ → ⟪ Γ ⊢ inBool n t : UVal (S n) ⟫.
Proof.
  unfold inBool. crushTyping.
Qed.

Definition inProd (n : nat) (t : Tm) : Tm := inr (inr (inr (inl t))).

Lemma inProd_T {Γ n t} : ⟪ Γ ⊢ t : UVal n × UVal n ⟫ → ⟪ Γ ⊢ inProd n t : UVal (S n) ⟫.
Proof.
  unfold inProd. crushTyping.
Qed.

Definition inArr (n : nat) (t : Tm) : Tm := inr (inr (inr (inr (inl t)))).

Lemma inArr_T {Γ n t} : ⟪ Γ ⊢ t : UVal n ⇒ UVal n ⟫ → ⟪ Γ ⊢ inArr n t : UVal (S n) ⟫.
Proof.
  unfold inArr. crushTyping.
Qed.

Definition inSum (n : nat) (t : Tm) : Tm := inr (inr (inr (inr (inr t)))).

Lemma inSum_T {Γ n t} : ⟪ Γ ⊢ t : UVal n ⊎ UVal n ⟫ → ⟪ Γ ⊢ inSum n t : UVal (S n) ⟫.
Proof.
  unfold inSum. crushTyping.
Qed.

Definition caseV0 (case₁ : Tm) (case₂ : Tm) :=
  caseof (var 0) (case₁ [wk↑]) (case₂[wk↑]).

Definition caseUVal (n : nat) (tscrut tunk tcunit tcbool tcprod tcsum tcarr : Tm) :=
  caseof tscrut
         (tunk [wk])
         (caseV0 tcunit
                 (caseV0 tcbool
                         (caseV0 tcprod
                                 (caseV0 tcarr tcsum)))).

Lemma caseV0_T {Γ τ₁ τ₂ τ case₁ case₂} :
  ⟪ Γ ▻ τ₁ ⊢ case₁ : τ ⟫ →
  ⟪ Γ ▻ τ₂ ⊢ case₂ : τ ⟫ →
  ⟪ Γ ▻ (τ₁ ⊎ τ₂) ⊢ caseV0 case₁ case₂ : τ ⟫.
Proof.
  unfold caseV0.
  crushTyping.
Qed.


Lemma caseUVal_T {Γ n tscrut tunk tcunit tcbool tcprod tcsum tcarr τ} :
  ⟪ Γ ⊢ tscrut : UVal (S n) ⟫ →
  ⟪ Γ ⊢ tunk : τ ⟫ →
  ⟪ Γ ▻ tunit ⊢ tcunit : τ ⟫ →
  ⟪ Γ ▻ tbool ⊢ tcbool : τ ⟫ →
  ⟪ Γ ▻ (UVal n × UVal n) ⊢ tcprod : τ ⟫ →
  ⟪ Γ ▻ (UVal n ⊎ UVal n) ⊢ tcsum : τ ⟫ →
  ⟪ Γ ▻ (UVal n ⇒ UVal n) ⊢ tcarr : τ ⟫ →
  ⟪ Γ ⊢ caseUVal n tscrut tunk tcunit tcbool tcprod tcsum tcarr : τ ⟫.
Proof.
  unfold caseUVal.
  crushTyping.
  repeat apply caseV0_T;
  crushTyping.
Qed.