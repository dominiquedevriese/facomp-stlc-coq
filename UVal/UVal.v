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

Lemma unkUVal_Value {n : nat} : Value (unkUVal n).
Proof.
  destruct n; simpl; trivial.
Qed.

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

Lemma canonUVal {n v} :
  ⟪ empty ⊢ v : UVal (S n) ⟫ → Value v →
  (v = unkUVal (S n)) ∨
  (∃ v', v = inUnit n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tunit ⟫) ∨
  (∃ v', v = inBool n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tbool ⟫) ∨
  (∃ v', v = inProd n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n × UVal n ⟫) ∨
  (∃ v', v = inSum n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n ⊎ UVal n ⟫) ∨
  (∃ v', v = inArr n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n ⇒ UVal n ⟫).
Proof.
  intros ty vv.
  unfold UVal in ty; simpl. 
  (* Apply canonical form lemmas but only as far as we need. *)
  stlcCanForm1; 
    [left|right;stlcCanForm1;
       [left|right;stlcCanForm1;
          [left|right;stlcCanForm1;
                [left|right;stlcCanForm1;
                      [right|left]]]]]. 
  - stlcCanForm; crush.
  - exists x0; crush.
  - exists x; crush.
  - exists x0; crush.
  - exists x; crush.
  - exists x; crush.
Qed. 

Lemma caseUVal_eval_unk {n tunk tcunit tcbool tcprod tcsum tcarr} :
  caseUVal n (unkUVal (S n)) tunk tcunit tcbool tcprod tcsum tcarr -->* tunk.
Proof.
  unfold caseUVal, unkUVal.
  (* why doesn't crush do the following? *)
  assert (Value (inl unit)) by (simpl; trivial).
  crushEvalsInCaseUVal.
Qed.
  
Lemma caseUVal_eval_unit {n tunk tcunit tcbool tcprod tcsum tcarr v} :
  Value v →
  caseUVal n (inUnit n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcunit [beta1 v].
Proof.
  intros vv.
  unfold caseUVal, inUnit.
  crushEvalsInCaseUVal.
Qed.
  
Lemma caseUVal_eval_bool {n tunk tcunit tcbool tcprod tcsum tcarr v} :
  Value v →
  caseUVal n (inBool n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcbool [beta1 v].
Proof.
  intros vv.
  unfold caseUVal, inBool.
  crushEvalsInCaseUVal.
Qed.
  
Lemma caseUVal_eval_prod {n tunk tcunit tcbool tcprod tcsum tcarr v} :
  Value v →
  caseUVal n (inProd n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcprod [beta1 v].
Proof.
  intros vv.
  unfold caseUVal, inProd.
  crushEvalsInCaseUVal.
Qed.

Lemma caseUVal_eval_sum {n tunk tcunit tcbool tcprod tcsum tcarr v} :
  Value v →
  caseUVal n (inSum n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcsum [beta1 v].
Proof.
  intros vv.
  unfold caseUVal, inSum.
  crushEvalsInCaseUVal.
Qed.

Lemma caseUVal_eval_arr {n tunk tcunit tcbool tcprod tcsum tcarr v} :
  Value v →
  caseUVal n (inArr n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcarr [beta1 v].
Proof.
  intros vv.
  unfold caseUVal, inArr.
  crushEvalsInCaseUVal.
Qed.

Lemma caseUVal_sub {n t tunk tcunit tcbool tcprod tcsum tcarr} γ :
  (caseUVal n t tunk tcunit tcbool tcprod tcsum tcarr)[γ] =
  caseUVal n (t[γ]) (tunk[γ]) (tcunit[γ↑]) (tcbool[γ↑]) (tcprod[γ↑]) (tcsum[γ↑]) (tcarr[γ↑]).
Proof.
  unfold caseUVal, caseV0. cbn. 
  crush; 
    rewrite <- ?apply_wkm_comm, <- ?(apply_wkm_up_comm); 
    reflexivity.
Qed.  


Arguments caseUVal n tscrut tunk tcunit tcbool tcprod tcsum tcarr : simpl never.