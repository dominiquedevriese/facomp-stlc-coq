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

Definition inUnit (n : nat) : Tm := abs tunit (inr (inl (var 0))).

Lemma inUnitT {Γ n} : ⟪ Γ ⊢ inUnit n : tunit ⇒ UVal (S n) ⟫.
Proof.
  unfold inUnit. crushTyping.
Qed.

Definition inBool (n : nat) : Tm := abs tbool (inr (inr (inl (var 0)))).

Lemma inBoolT {Γ n} : ⟪ Γ ⊢ inBool n : tbool ⇒ UVal (S n) ⟫.
Proof.
  unfold inBool. crushTyping.
Qed.

Definition inProd (n : nat) : Tm := abs (UVal n × UVal n) (inr (inr (inr (inl (var 0))))).

Lemma inProd_T {Γ n} : ⟪ Γ ⊢ inProd n : (UVal n × UVal n) ⇒ UVal (S n) ⟫.
Proof.
  unfold inProd. crushTyping.
Qed.

Definition inArr (n : nat) : Tm := abs (UVal n ⇒ UVal n) (inr (inr (inr (inr (inl (var 0)))))).

Lemma inArr_T {Γ n} : ⟪ Γ ⊢ inArr n : (UVal n ⇒ UVal n) ⇒ UVal (S n) ⟫.
Proof.
  unfold inArr. crushTyping.
Qed.

Definition inSum (n : nat) : Tm := abs (UVal n ⊎ UVal n) (inr (inr (inr (inr (inr (var 0)))))).

Lemma inSum_T {Γ n} : ⟪ Γ ⊢ inSum n : (UVal n ⊎ UVal n) ⇒ UVal (S n) ⟫.
Proof.
  unfold inSum. crushTyping.
Qed.


(* Local Variables: *)
(* coq-load-path: (("." "UVal") ("../Stlc" "Stlc")) *)
(* End: *)
