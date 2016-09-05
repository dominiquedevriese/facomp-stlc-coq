Require Import Stlc.SpecEvaluation.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.CanForm.
Require Import Common.Relations.

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
  unfold inUnit. crushTyping.
Qed.

Arguments inUnit n t : simpl never.

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
  caseof (var 0) (case₁ [wkm↑]) (case₂[wkm↑]).

Definition caseUVal (n : nat) (tscrut tunk tcunit tcbool tcprod tcsum tcarr : Tm) :=
  caseof tscrut
         (tunk [wkm])
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

Hint Resolve caseV0_T : uval_typing.

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
  eauto with typing uval_typing.
Qed.

Arguments UVal n : simpl never.
Hint Resolve unkUValT : uval_typing.
Hint Resolve inUnitT : uval_typing.
Hint Resolve inBoolT : uval_typing.
Hint Resolve inProd_T : uval_typing.
Hint Resolve inSum_T : uval_typing.
Hint Resolve inArr_T : uval_typing.
Hint Resolve caseUVal_T : uval_typing.

Local Ltac crush :=
  repeat (subst*;
          repeat rewrite
          (*   ?protect_wkm_beta1, ?protect_wkm2_beta1, *)
          (*   ?confine_wkm_beta1, ?confine_wkm2_beta1, *)
           ?apply_wkm_beta1_up_cancel;
          (*   ?apply_up_def_S; *)
          repeat crushDbLemmasMatchH;
          repeat crushDbSyntaxMatchH;
          repeat crushStlcSyntaxMatchH;
          repeat crushTypingMatchH2;
          repeat crushTypingMatchH;
          repeat match goal with
                     [ |- _ ∧ _ ] => split
                 end;
          trivial; 
          eauto with ws typing uval_typing eval
         ).

Lemma caseV0_eval_inl {v case₁ case₂}:
  Value v →
  (caseV0 case₁ case₂)[beta1 (inl v)] --> case₁ [beta1 v].
Proof.
  intros vv.
  unfold caseV0; apply eval₀_to_eval; crush.
  change ((caseof (var 0) case₁[wkm↑] case₂ [wkm↑])[beta1 (inl v)]) with
  (caseof (inl v) (case₁[wkm↑][(beta1 (inl v))↑]) (case₂[wkm↑][(beta1 (inl v))↑])).
  crush.
Qed.
  
Lemma caseV0_eval_inr {v case₁ case₂}:
  Value v →
  (caseV0 case₁ case₂)[beta1 (inr v)] --> case₂ [beta1 v].
Proof.
  intros vv.
  unfold caseV0; apply eval₀_to_eval; crush.
  change ((caseof (var 0) case₁[wkm↑] case₂ [wkm↑])[beta1 (inr v)]) with
  (caseof (inr v) (case₁[wkm↑][(beta1 (inr v))↑]) (case₂[wkm↑][(beta1 (inr v))↑])).
  crush.
Qed.
  
Lemma caseV0_eval {v τ₁ τ₂ case₁ case₂}:
  Value v → ⟪ empty ⊢ v : τ₁ ⊎ τ₂ ⟫ →
  (exists v', v = inl v' ∧ (caseV0 case₁ case₂)[beta1 v] --> case₁ [beta1 v']) ∨
  (exists v', v = inr v' ∧ (caseV0 case₁ case₂)[beta1 v] --> case₂ [beta1 v']).
Proof.
  intros vv ty.
  stlcCanForm; [left|right]; exists x; 
  crush; eauto using caseV0_eval_inl, caseV0_eval_inr.
Qed.
  
Local Ltac crushEvalsInCaseUVal :=
  repeat 
    (match goal with
         [ |- caseof (inl _) _ _ -->* _ ] => (eapply (evalStepStar _); [eapply eval₀_to_eval; crush|])
       | [ |- caseof (inr _) _ _ -->* _ ] => (eapply (evalStepStar _); [eapply eval₀_to_eval; crush|])
       | [ |- (caseV0 _ _) [beta1 (inl _)] -->* _ ] => (eapply (evalStepStar _); [eapply caseV0_eval_inl; crush|])
       | [ |- (caseV0 _ _) [beta1 (inr _)] -->* _ ] => (eapply (evalStepStar _); [eapply caseV0_eval_inr; crush|])
       | [ |- ?t -->* ?t ] => eauto with eval
     end;
     try rewrite -> apply_wkm_beta1_cancel
    ).

Lemma caseUVal_eval {n v tunk tcunit tcbool tcprod tcsum tcarr} :
  ⟪ empty ⊢ v : UVal (S n) ⟫ → Value v →
  let t := caseUVal n v tunk tcunit tcbool tcprod tcsum tcarr in
  (v = unkUVal (S n) ∧ t -->* tunk) ∨
  (∃ v', v = inUnit n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tunit ⟫ ∧ t -->* tcunit[beta1 v']) ∨
  (∃ v', v = inBool n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tbool ⟫ ∧ t -->* tcbool[beta1 v']) ∨
  (∃ v', v = inProd n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n × UVal n ⟫ ∧ t -->* tcprod[beta1 v']) ∨
  (∃ v', v = inSum n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n ⊎ UVal n ⟫ ∧ t -->* tcsum[beta1 v']) ∨
  (∃ v', v = inArr n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n ⇒ UVal n ⟫ ∧ t -->* tcarr[beta1 v']).
Proof.
  intros ty vv.
  unfold UVal in ty; simpl; unfold caseUVal. 
  (* Apply canonical form lemmas but only as far as we need. *)
  stlcCanForm1; 
    [left|right;stlcCanForm1;
       [left|right;stlcCanForm1;
          [left|right;stlcCanForm1;
                [left|right;stlcCanForm1;
                      [right|left]]]]]. 
  - stlcCanForm. crush.
    crushEvalsInCaseUVal.
  - stlcCanForm; exists unit; crush.
    crushEvalsInCaseUVal.
  - exists x; crush.
    crushEvalsInCaseUVal.
  - exists x0; crush.
    crushEvalsInCaseUVal.
  - exists x; crush.
    crushEvalsInCaseUVal.
  - exists x; crush.
    crushEvalsInCaseUVal.
Qed.