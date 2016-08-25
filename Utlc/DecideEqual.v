Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecScoping.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.Inst.

Require Import Coq.Logic.Decidable.
Require Import Coq.Arith.Peano_dec.

Lemma decide_eq_UTm (tu tu' : UTm) : {tu = tu'} + {tu <> tu'}.
Proof.
  unfold decidable.
  decide equality.
  destruct (eq_nat_dec i i0); [left|right]; intuition.
Qed.

