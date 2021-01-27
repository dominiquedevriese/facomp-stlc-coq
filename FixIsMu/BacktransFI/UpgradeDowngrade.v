Require Import UValFI.UVal.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.Contraction.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.Inst.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRelFI.LRFI.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import LogRelFI.LemmasInversion.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.PseudoTypeFI.

Require Import Lia.

Require Import Program.Wf.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushRepEmulEmbed;
     repeat I.crushStlcSyntaxMatchH;
     repeat F.crushStlcSyntaxMatchH;
     split;
     trivial;
     crushTyping;
     try crushOfType;
     subst*);
  try discriminate; try lia;
  eauto with eval;
  repeat crushStlcSyntaxMatchH (* remove apTm's again *).

Inductive FullContr : I.Ty → Prop :=
  | FullContrPrim : FullContr I.tunit
  | FullContrArr {τ τ'} :
      FullContr τ →
      FullContr τ' →
      FullContr (I.tarr τ τ')
  | FullContrSum {τ τ'} :
      FullContr τ →
      FullContr τ' →
      FullContr (I.tsum τ τ')
  | FullContrRec {τ} :
      FullContr τ →
      FullContr (I.trec τ).

Lemma FullContr_implies_Contr {τ} : FullContr τ → Contr τ.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma Contr_implies_FuContr {τ P} : Contr τ → Contr (fu τ P).
Admitted.

Lemma FullContr_implies_FuFullContr {τ P} : FullContr τ → FullContr (fu τ P).
Admitted.


Fixpoint downgrade (n : nat) (d : nat) (τ : I.Ty) {struct n} : F.Tm :=
  let abs_creator := F.abs (UValFI (n + d) τ) in
  match n with
    | 0 => abs_creator (unkUVal 0)
    | S n =>
      match τ with
        | I.tunit => abs_creator (F.var 0)
        | I.tsum τ τ' => abs_creator (F.caseof (F.var 0)
                                              (F.inl (F.caseof (F.var 0)
                                                               (F.inl (F.app (downgrade n d τ)
                                                                             (F.var 0)))
                                                               (F.inr (F.app (downgrade n d τ')
                                                                             (F.var 0)))))
                                              (F.inr (F.var 0)))
        | I.tarr τ τ' => abs_creator (F.caseof (F.var 0)
                                              (F.inl (F.abs (UValFI n τ)
                                                            (F.app (downgrade n d τ')
                                                                   (F.app (F.var 1)
                                                                          (F.app (upgrade n d τ)
                                                                                 (F.var 0))))))
                                              (F.inr (F.var 0)))
        (* this should really be downgrade n+1 but use the guarantee of non-recursion *)
        | I.trec τ' => downgrade n d (fu' (I.trec τ'))
        | I.tvar _ => F.unit
      end
  end
with
upgrade (n : nat) (d : nat) (τ : I.Ty) {struct n} :=
  let abs_creator := F.abs (UValFI n τ) in
  match n with
    | 0 => abs_creator (unkUVal d)
    | S n =>
      match τ with
        | I.tunit => abs_creator (F.var 0)
        | I.tsum τ τ' => abs_creator (F.caseof (F.var 0)
                                        (F.inl (F.caseof (F.var 0)
                                                          (F.inl (F.app (upgrade n d τ)
                                                                        (F.var 0)))
                                                          (F.inr (F.app (upgrade n d τ')
                                                                        (F.var 0)))))
                                        (F.inr (F.var 0)))
        | I.tarr τ τ' => abs_creator (F.caseof (F.var 0)
                                              (F.inl (F.abs (UValFI n τ)
                                                            (F.app (upgrade n d τ')
                                                                  (F.app (F.var 1)
                                                                          (F.app (downgrade n d τ)
                                                                                (F.var 0))))))
                                              (F.inr (F.var 0)))
        | I.trec τ' => upgrade n d (fu' (I.trec τ'))
        | I.tvar _ => F.unit
        end
  end.

(* Lemma upgrade_arr_T {n : nat} {Γ d τ τ'} : *)
(*   ⟪ Γ ⊢ upgrade n d τ' : UValFI n τ' ⇒ UValFI (n + d) τ' ⟫ → *)
(*   ⟪ Γ ⊢ downgrade n d τ : UValFI (n + d) τ ⇒ UValFI n τ ⟫ → *)
(*   ⟪ Γ ⊢ upgrade n d (I.tarr τ τ') : UValFI n (I.tarr τ τ') ⇒ UValFI (n + d) (I.tarr τ τ') ⟫. *)
(* Proof. *)
(*   intros. *)
(*   induction n. *)
(*   eauto with typing uval_typing. *)
(*   unfold upgrade. *)
(*   constructor. *)
(*   econstructor. *)
(*   constructor. *)
(*   unfold UValFI. *)
(*   eauto with typing uval_typing. *)
(* downgrade_T {n : nat} {Γ d τ} : *)
(*   ⟪ Γ ⊢ downgrade n d (I.tarr τ1 τ2) : UValFI (n + d) τ ⇒ UValFI n τ ⟫. *)

Lemma upgrade_T {n : nat} {Γ d τ} :
  ⟪ Γ ⊢ upgrade n d τ : UValFI n τ ⇒ UValFI (n + d) τ ⟫
with
downgrade_T {n : nat} {Γ d τ} :
  ⟪ Γ ⊢ downgrade n d τ : UValFI (n + d) τ ⇒ UValFI n τ ⟫.
Proof.
  (* can I combine eauto and crushTyping somehow? *)
  - induction n.
    unfold upgrade, downgrade.
    eauto with typing uval_typing.
    (* unfold upgrade, downgrade. *)
    eauto with typing uval_typing.
  - induction n.
    unfold upgrade, downgrade.
    eauto with typing uval_typing.
    eauto with typing uval_typing.
Admitted.

Lemma upgrade_T1 {Γ n τ} :
  ⟪ Γ ⊢ upgrade n 1 τ : UValFI n τ ⇒ UValFI (S n) τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using upgrade_T.
Qed.

Lemma downgrade_T1 {Γ n τ} :
  ⟪ Γ ⊢ downgrade n 1 τ : UValFI (S n) τ ⇒ UValFI n τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using downgrade_T.
Qed.

Hint Resolve upgrade_T1 : uval_typing.
Hint Resolve downgrade_T1 : uval_typing.

Lemma upgrade_closed {n d τ} :
  ⟨ 0 ⊢ upgrade n d τ ⟩.
Proof.
  enough (⟪ empty ⊢ upgrade n d τ : UValFI n τ ⇒ UValFI (n + d) τ ⟫) as ty by eapply (wt_implies_ws ty).
  eapply upgrade_T.
Qed.

Lemma downgrade_closed {n d τ} :
  ⟨ 0 ⊢ downgrade n d τ ⟩.
Proof.
  enough (⟪ empty ⊢ downgrade n d τ : UValFI (n + d) τ ⇒ UValFI n τ ⟫) as ty by eapply (wt_implies_ws ty).
  eapply downgrade_T.
Qed.

Lemma upgrade_sub {n d τ γ} : (upgrade n d τ)[γ] = upgrade n d τ.
Proof.
  apply wsClosed_invariant.
  eapply upgrade_closed.
Qed.

Lemma downgrade_sub {n d τ γ} : (downgrade n d τ)[γ] = downgrade n d τ.
Proof.
  apply wsClosed_invariant.
  eapply downgrade_closed.
Qed.

Lemma downgrade_value {n d τ} : Value (downgrade n d τ).
Proof.
  revert d τ;
  induction n; destruct τ; simpl; trivial.
Qed.

Lemma upgrade_value {n d τ} : Value (upgrade n d τ).
Proof.
  revert d τ;
  induction n; destruct τ; simpl; trivial.
Qed.

Lemma downgrade_zero_eval {d τ v} : Value v → app (downgrade 0 d τ) v -->* unkUVal 0.
Proof.
  intros vv.
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  simpl; eauto with eval.
Qed.

Lemma upgrade_zero_eval {d τ v} : Value v → app (upgrade 0 d τ) v -->* unkUVal d.
Proof.
  intros vv.
  unfold upgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  destruct d; simpl; eauto with eval.
Qed.

Lemma downgrade_eval_unk {n d τ} : app (downgrade n d τ) (unkUVal (n + d)) -->* unkUVal n.
Proof.
  assert (vv : Value (unkUVal (n + d))) by apply unkUVal_Value.
  destruct n; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval. crush.
    simpl; eauto with eval.
  - change _ with (Value (inl unit)) in vv.
    eapply evalStepStar. eapply eval₀_to_eval.
    induction τ;
    crush.
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
    repeat (eapply evalStepStar; eapply eval₀_to_eval; crush).
Admitted.
    (* change (F.inl unit) with (unkUVal (S n)) at 1. *)
    (* eapply caseUVal_eval_unk. *)
(* Qed. *)

Lemma upgrade_eval_unk {n d τ} : app (upgrade n d τ) (unkUVal n) -->* unkUVal (n + d).
Proof.
  assert (vv : Value (unkUVal n)) by apply unkUVal_Value.
  revert τ.
  induction n; intro τ; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval. crush.
    destruct d; simpl; eauto with eval.
  - (* change _ with (Value (F.inr unit)) in vv. *)
    destruct τ.
    (eapply evalStepStar; [eapply eval₀_to_eval|idtac]);
    simpl;
    try (crush; fail).
    apply evalToStar.
    apply eval₀_to_eval.
    simpl.
    change (F.inr F.unit) with (F.inr (F.var 0))[beta1 F.unit].
    apply F.eval_case_inr.
    eauto.

    (eapply evalStepStar; [eapply eval₀_to_eval|idtac]);
    simpl;
    try (crush; fail).

    (eapply evalStepStar; [eapply eval₀_to_eval|idtac]);
    simpl;
    try (crush; fail).
    apply evalToStar.
    apply eval₀_to_eval.
    simpl.
    change (F.inr F.unit) with (F.inr (F.var 0))[beta1 F.unit].
    apply F.eval_case_inr.
    eauto.

    assert (vvp : Value (unkUVal n)) by apply unkUVal_Value.
    specialize (IHn vvp).
    change (F.inr F.unit) with (F.inr (F.var 0))[beta1 F.unit].
Admitted.

Lemma downgrade_eval_inUnit {n d} :
  app (downgrade (S n) d I.tunit) (F.inl F.unit) -->* F.inl F.unit.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply F.eval_beta.
  all: eauto with eval.
  crush.
Qed.
  (* eapply evalStepTrans. eapply caseUVal_eval_unit; crush. *)
  (* simpl; crush. *)
(* Qed. *)

Lemma upgrade_eval_inUnit {n d} :
  app (upgrade (S n) d I.tunit) (F.inl F.unit) -->* F.inl F.unit.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply F.eval_beta.
  all: eauto with eval.
  crush.
Qed.
  (* intros vv. *)
  (* assert (Value (F.inl v)) by (simpl; crush). *)
  (* unfold upgrade. *)
  (* eapply evalStepStar. eapply eval₀_to_eval. crush. *)
  (* rewrite -> ?(caseUVal_sub (beta1 _)); simpl. *)
  (* eapply evalStepTrans. eapply caseUVal_eval_unit; crush. *)
  (* simpl; crush. *)
(* Qed. *)

Lemma downgrade_eval_inBool {n d τ v} :
  Value v → app (downgrade (S n) d τ) (F.inl v) -->* F.inl v.
Proof.
  intros vv.
  assert (Value (F.inl v)) by (simpl; crush).
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
Admitted.
(*   eapply evalStepTrans. eapply caseUVal_eval_bool; crush. *)
(*   simpl; crush. *)
(* Qed. *)

Lemma upgrade_eval_inBool {n d τ v} :
  Value v → app (upgrade (S n) d τ) (F.inl v) -->* F.inl v.
Proof.
  intros vv.
  assert (Value (F.inl v)) by (simpl; crush).
  unfold upgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
Admitted.

(*   eapply evalStepTrans. eapply caseUVal_eval_bool; crush. *)
(*   simpl; crush. *)
(* Qed. *)

(* Lemma downgrade_eval_inProd {n d v₁ v₂ v₁' v₂'} :  *)
(*   Value v₁ → Value v₂ → Value v₁' → Value v₂' → *)
(*   app (downgrade n d) v₁ -->* v₁' → *)
(*   app (downgrade n d) v₂ -->* v₂' → *)
(*   app (downgrade (S n) d) (inProd (n + d) (pair v₁ v₂)) -->* inProd n (pair v₁' v₂'). *)
(* Proof. *)
(*   intros vv₁ vv₂ vv₁' vv₂' es₁ es₂. *)
(*   assert (Value (inProd (n + d) (pair v₁ v₂))) by (simpl; crush). *)
(*   unfold downgrade. *)
(*   assert (Value (downgrade n d)) by apply downgrade_value. *)

(*   (* beta-reduce *) *)
(*   eapply evalStepStar. eapply eval₀_to_eval; crush. *)
(*   rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush. *)
(*   rewrite -> ?upgrade_sub, ?downgrade_sub. *)

(*   (* evaluate UVal pattern match *) *)
(*   eapply evalStepTrans. eapply caseUVal_eval_prod; crush. *)
(*   (* downgrade under sub... *) *)
(*   simpl; crush. *)
(*   rewrite -> ?downgrade_sub. *)

(*   (* first projection *) *)
(*   eapply evalStepStar.  *)
(*   assert (ep₁ : proj₁ (pair v₁ v₂) -->₀ v₁) by crush. *)
(*   eapply (eval_from_eval₀ ep₁); inferContext; crush; simpl. *)

(*   (* recursive call 1 *) *)
(*   eapply evalStepTrans. eapply (evalstar_ctx' es₁); inferContext; crush. *)

(*   (* second projection *) *)
(*   eapply evalStepStar.  *)
(*   assert (ep₂ : proj₂ (pair v₁ v₂) -->₀ v₂) by crush. *)
(*   eapply (eval_from_eval₀ ep₂); inferContext; crush; simpl. *)

(*   (* recursive call 2 *) *)
(*   eapply evalStepTrans. eapply (evalstar_ctx' es₂); inferContext; crush. *)

(*   (* ... and we're done. *) *)
(*   simpl; crush. *)
(* Qed. *)

(* Lemma upgrade_eval_inProd {n d v₁ v₂ v₁' v₂'} :  *)
(*   Value v₁ → Value v₂ → Value v₁' → Value v₂' → *)
(*   app (upgrade n d) v₁ -->* v₁' → *)
(*   app (upgrade n d) v₂ -->* v₂' → *)
(*   app (upgrade (S n) d) (inProd n (pair v₁ v₂)) -->* inProd (n + d) (pair v₁' v₂'). *)
(* Proof. *)
(*   intros vv₁ vv₂ vv₁' vv₂' es₁ es₂. *)
(*   assert (Value (inProd (n + d) (pair v₁ v₂))) by (simpl; crush). *)
(*   unfold upgrade. *)
(*   assert (Value (upgrade n d)) by apply upgrade_value. *)

(*   (* beta-reduce *) *)
(*   eapply evalStepStar. eapply eval₀_to_eval; crush. *)
(*   rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush. *)
(*   rewrite -> ?upgrade_sub, ?upgrade_sub. *)

(*   (* evaluate UVal pattern match *) *)
(*   eapply evalStepTrans. eapply caseUVal_eval_prod; crush. *)
(*   (* upgrade under sub... *) *)
(*   simpl; crush. *)
(*   rewrite -> ?upgrade_sub. *)

(*   (* first projection *) *)
(*   eapply evalStepStar.  *)
(*   assert (ep₁ : proj₁ (pair v₁ v₂) -->₀ v₁) by crush. *)
(*   eapply (eval_from_eval₀ ep₁); inferContext; crush; simpl. *)

(*   (* recursive call 1 *) *)
(*   eapply evalStepTrans. eapply (evalstar_ctx' es₁); inferContext; crush. *)

(*   (* second projection *) *)
(*   eapply evalStepStar.  *)
(*   assert (ep₂ : proj₂ (pair v₁ v₂) -->₀ v₂) by crush. *)
(*   eapply (eval_from_eval₀ ep₂); inferContext; crush; simpl. *)

(*   (* recursive call 2 *) *)
(*   eapply evalStepTrans. eapply (evalstar_ctx' es₂); inferContext; crush. *)

(*   (* ... and we're done. *) *)
(*   simpl; crush. *)
(* Qed. *)

(* Lemma downgrade_eval_inSum {n d v v' va va'} : *)
(*   Value v → Value v' → *)
(*   (va = inl v ∧ va' = inl v') ∨ (va = inr v ∧ va' = inr v') → *)
(*   app (downgrade n d) v -->* v' → *)
(*   app (downgrade (S n) d) (inSum (n + d) va) -->* inSum n va'. *)
(* Proof. *)
(*   intros vv vv' eqs es. *)

(*   unfold downgrade. *)
(*   destruct eqs as [(? & ?)|(? & ?)]; subst; *)
(*   (* beta-reduce *) *)
(*   (eapply evalStepStar; [eapply eval₀_to_eval; crush|]); *)
(*     rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush; *)
(*     rewrite -> ?upgrade_sub, ?downgrade_sub; *)

(*     (* evaluate UVal pattern match *) *)
(*     (eapply evalStepTrans; [eapply caseUVal_eval_sum; crush|]); *)
(*     (* downgrade under sub... *) *)
(*     simpl; crush; *)
(*     rewrite -> ?downgrade_sub; *)

(*     (* caseof *) *)
(*     [assert (ec : caseof (inl v) (inl (app (downgrade n d) (var 0))) (inr (app (downgrade n d) (var 0))) -->₀ ((inl (app (downgrade n d) (var 0))) [beta1 v])) by crush *)
(*     |assert (ec : caseof (inr v) (inl (app (downgrade n d) (var 0))) (inr (app (downgrade n d) (var 0))) -->₀ ((inr (app (downgrade n d) (var 0))) [beta1 v])) by crush *)
(*     ]; *)
(*     (eapply evalStepStar; *)
(*      [eapply (eval_from_eval₀ ec); inferContext; crush|]); *)
(*     crushStlcSyntaxMatchH (* why is this needed? *); *)
(*     rewrite -> ?downgrade_sub; *)

(*     (* recursive call *) *)
(*     (eapply evalStepTrans; [eapply (evalstar_ctx' es); inferContext; crush|]); *)

(*     (* ... and we're done. *) *)
(*     simpl; crush. *)
(* Qed. *)

(* Lemma upgrade_eval_inSum {n d v v' va va'} :  *)
(*   Value v → Value v' →  *)
(*   (va = inl v ∧ va' = inl v') ∨ (va = inr v ∧ va' = inr v') → *)
(*   app (upgrade n d) v -->* v' → *)
(*   app (upgrade (S n) d) (inSum n va) -->* inSum (n + d) va'. *)
(* Proof. *)
(*   intros vv vv' eqs es. *)

(*   unfold upgrade. *)
(*   destruct eqs as [(? & ?)|(? & ?)]; subst; *)
(*   (* beta-reduce *) *)
(*   (eapply evalStepStar; [eapply eval₀_to_eval; crush|]); *)
(*     rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush; *)
(*     rewrite -> ?upgrade_sub, ?upgrade_sub; *)

(*     (* evaluate UVal pattern match *) *)
(*     (eapply evalStepTrans; [eapply caseUVal_eval_sum; crush|]); *)
(*     (* upgrade under sub... *) *)
(*     simpl; crush; *)
(*     rewrite -> ?upgrade_sub; *)

(*     (* caseof *) *)
(*     [assert (ec : caseof (inl v) (inl (app (upgrade n d) (var 0))) (inr (app (upgrade n d) (var 0))) -->₀ ((inl (app (upgrade n d) (var 0))) [beta1 v])) by crush *)
(*     |assert (ec : caseof (inr v) (inl (app (upgrade n d) (var 0))) (inr (app (upgrade n d) (var 0))) -->₀ ((inr (app (upgrade n d) (var 0))) [beta1 v])) by crush *)
(*     ]; *)
(*     (eapply evalStepStar; *)
(*      [eapply (eval_from_eval₀ ec); inferContext; crush|]); *)
(*     crushStlcSyntaxMatchH (* why is this needed? *); *)
(*     rewrite -> ?upgrade_sub; *)

(*     (* recursive call *) *)
(*     (eapply evalStepTrans; [eapply (evalstar_ctx' es); inferContext; crush|]); *)

(*     (* ... and we're done. *) *)
(*     simpl; crush. *)
(* Qed. *)

(* Lemma downgrade_eval_inArr {n d v} :  *)
(*   Value v → *)
(*   app (downgrade (S n) d) (inArr (n + d) v) -->*  *)
(*       inArr n (abs (UVal n) (app (downgrade n d) (app (v[wk]) (app (upgrade n d) (var 0))))). *)
(* Proof. *)
(*   intros vv. *)
(*   unfold downgrade. *)

(*   (* beta-reduce *) *)
(*   (eapply evalStepStar; [eapply eval₀_to_eval; crush|]); *)
(*   rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush; *)
(*   rewrite -> ?upgrade_sub, ?downgrade_sub. *)

(*   (* evaluate UVal pattern match *) *)
(*   (eapply evalStepTrans; [eapply caseUVal_eval_arr; crush|]); *)
(*     (* downgrade under sub... *) *)
(*     simpl; crush; *)
(*     rewrite -> ?downgrade_sub, ?upgrade_sub. *)

(*   change (wk 0) with 1; simpl. *)
(*   eauto with eval. *)
(* Qed. *)

(* Lemma upgrade_eval_inArr {n d v} :  *)
(*   Value v → *)
(*   app (upgrade (S n) d) (inArr n v) -->*  *)
(*       inArr (n + d) (abs (UVal (n + d)) (app (upgrade n d) (app (v[wk]) (app (downgrade n d) (var 0))))). *)
(* Proof. *)
(*   intros vv. *)
(*   unfold upgrade; simpl. *)

(*   (* beta-reduce *) *)
(*   (eapply evalStepStar; [eapply eval₀_to_eval; crush|]). *)
(*   rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush; *)
(*   rewrite -> ?upgrade_sub, ?downgrade_sub. *)

(*   (* evaluate UVal pattern match *) *)
(*   (eapply evalStepTrans; [eapply caseUVal_eval_arr; crush|]); *)
(*     (* upgrade under sub... *) *)
(*     simpl; crush; *)
(*     rewrite -> ?upgrade_sub, ?downgrade_sub. *)

(*   change (wk 0) with 1; simpl. *)
(*   eauto with eval. *)
(* Qed. *)


Lemma downgrade_reduces {n d v τ} :
  ⟪ empty ⊢ v : UValFI (n + d) τ ⟫ → Value v →
  exists v', Value v' ∧ ⟪ empty ⊢ v' : UValFI n τ ⟫ ∧
             app (downgrade n d τ) v -->* v'.
Proof.
  revert τ;
  revert v; induction n;
  intros v τ ty vv.
  - exists (unkUVal 0).
    eauto using unkUVal_Value, unkUValT, downgrade_zero_eval.
  - change (S n + d) with (S (n + d)) in ty.
    destruct τ.
    + destruct (canonUValS_Arr vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (F.can_form_tarr H H1).
        exists (F.inl (F.abs (UValFI n τ1) (F.app (downgrade n d τ2)
                                             (F.app x
                                                    (F.app (upgrade n d τ1)
                                                           (* x))))). *)
                                                           (F.var 0)))))).
        repeat split.
        replace x with x [wk] by (eapply wsClosed_invariant;
                                  refine (F.wt_implies_ws H1)).
        eauto using downgrade_T, upgrade_T with typing ws.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); eauto.
        cbn; crush; rewrite downgrade_sub, upgrade_sub.
        change ((beta1 x)↑ (wk 0)) with x [wk].
        replace x[wk] with x; [econstructor|].
        eapply eq_sym, wsClosed_invariant.
        refine (F.wt_implies_ws H1).
        (* eauto using inArr_Value, downgrade_eval_inArr, inArr_T,  *)
        (* downgrade_T, upgrade_T with typing. *)
      * 
Qed.

Lemma upgrade_reduces {n v} d :
  ⟪ empty ⊢ v : UVal n ⟫ → Value v →
  exists v', Value v' ∧ ⟪ empty ⊢ v' : UVal (n + d) ⟫ ∧ 
             app (upgrade n d) v -->* v'.
Proof.
  revert v; induction n;
  intros v ty vv.
  - exists (unkUVal d).
    eauto using unkUVal_Value, unkUValT, upgrade_zero_eval.
  - canonUVal. 
    + exists (unkUVal (S (n + d))).
      change (S (n + d)) with (S n + d).
      eauto using unkUVal_Value, unkUValT, upgrade_eval_unk.
    + exists (inUnit (n + d) x).
      eauto using inUnit_Value, inUnitT, upgrade_eval_inUnit.
    + exists (inBool (n + d) x).
      eauto using inBool_Value, inBoolT, upgrade_eval_inBool.
    + stlcCanForm.
      destruct H0 as (vx0 & vx1).
      destruct (IHn _ H2 vx0) as (x0' & vx0' & ty0 & evalx0).
      destruct (IHn _ H3 vx1) as (x1' & vx1' & ty1 & evalx1).
      exists (inProd (n + d) (pair x0' x1')).
      assert (Value (pair x0' x1')) by crush.
      change (S n + d) with (S (n + d)).
      eauto using inProd_Value, inProd_T, upgrade_eval_inProd with typing.
    + stlcCanForm;
      [ destruct (IHn _ H2 H0) as (vf & vvf & tyf & ex);
        exists (inSum (n + d) (inl vf))
      | destruct (IHn _ H2 H0) as (vf & vvf & tyf & ex);
        exists (inSum (n + d) (inr vf))];
      repeat split;
      eauto using inSum_Value, inSum_T, upgrade_eval_inSum with typing.
    + exists (inArr (n + d) (abs (UVal (n + d)) (app (upgrade n d) (app (x[wk]) (app (downgrade n d) (var 0)))))).
      assert (Value (abs (UVal (n + d)) (app (upgrade n d) (app (x[wk]) (app (downgrade n d) (var 0)))))) by crush.
      repeat split;
      eauto using inArr_Value, upgrade_eval_inArr, inArr_T, 
            upgrade_T, downgrade_T with typing.
Qed.
  
  
Definition dir_world_prec (n : nat) (w : World) (d : Direction) (p : Prec) : Prop :=
  (lev w < n ∧ p = precise) ∨ (d = dir_lt ∧ p = imprecise).

Arguments dir_world_prec n w d p : simpl never.

Lemma dwp_zero {w d p} : dir_world_prec 0 w d p → p = imprecise ∧ d = dir_lt.
Proof.
  destruct 1 as [[? ?]|[? ?]].
  - depind H.
  - auto.
Qed.

Lemma dwp_precise {n d w} : lev w < n → dir_world_prec n w d precise.
Proof.
  left; auto.
Qed.

Lemma dwp_imprecise {n w} : dir_world_prec n w dir_lt imprecise.
Proof.
  right; auto.
Qed.

Lemma dwp_invert_imprecise {n w d} : dir_world_prec n w d imprecise → d = dir_lt.
Proof.
  destruct 1 as [[? ?]|[? ?]].
  - inversion H0.
  - auto.
Qed.

Lemma dwp_invert_S {w d p n} : dir_world_prec (S n) (S w) d p → dir_world_prec n w d p.
Proof.
  destruct 1 as [[? ?]|[? ?]]; [left|right];
  eauto with arith.
Qed.

Lemma dwp_invert_S' {w d p n} : 
  dir_world_prec (S n) w d p → 
  forall w', w' < w → dir_world_prec n w' d p.
Proof.
  destruct 1 as [[? ?]|[? ?]]; [left|right];
  eauto with arith.
Qed.

Lemma dwp_mono {w d p n} : 
  dir_world_prec n w d p → 
  forall w', w' ≤ w → dir_world_prec n w' d p.
Proof.
  destruct 1 as [[? ?]|[? ?]]; [left|right];
  eauto with arith.
Qed.


Lemma downgrade_inProd_works {n d w dir p vs vu} :
  valrel dir w (pEmulDV (S (n + d)) p) (inProd (n + d) vs) vu →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV (n + d) p) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p) vs₁' vu₁) →
  exists v', 
    app (downgrade (S n) d) (inProd (n + d) vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p) v' vu.
Proof.
  intros vr ih.
  destruct (valrel_implies_OfType vr) as [[? ?] ?].
  destruct (invert_valrel_pEmulDV_inProd' vr) as (vs₁ & vs₂ & vu₁ & vu₂ & ? & ? & vr₁ & vr₂); subst.
  destruct w.
  * (* w = 0 *)
    destruct H1 as (wsPair & vpair).
    simpl in H0.
    canonUVal; crush.
    stlcCanForm.
    inversion H1; subst; clear H1.
    destruct_conjs; destruct H2 as [vx vx0].
    destruct (downgrade_reduces H4 vx) as (vs₁' & vvs₁' & ty₁' & es₁).
    destruct (downgrade_reduces H6 vx0) as (vs₂' & vvs₂' & ty₂' & es₂).
    exists (inProd n (S.pair vs₁' vs₂')).
    assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p) vs₁' vu₁) by (intros; exfalso; Omega.omega).
    assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p) vs₂' vu₂) by (intros; exfalso; Omega.omega).
    split.
    eapply downgrade_eval_inProd; crush.
    eapply valrel_inProd; crush.
  * (* w = S w *)
    assert (wlt : w < S w) by eauto with arith.
    assert (h1 := ih w vs₁ vu₁ wlt (vr₁ w wlt)).
    assert (h2 := ih w vs₂ vu₂ wlt (vr₂ w wlt)).
    destruct h1 as (vs₁' & es₁ & vr₁').
    destruct h2 as (vs₂' & es₂ & vr₂').
    destruct (valrel_implies_Value vr₁').
    destruct (valrel_implies_Value vr₂').
    exists (inProd n (S.pair vs₁' vs₂')).
    destruct H.
    eauto using downgrade_eval_inProd, valrel_inProd'.
Qed. 

Lemma upgrade_inProd_works {n d w dir p vs vu} :
  valrel dir w (pEmulDV (S n) p) (inProd n vs) vu →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV n p) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p) vs₁' vu₁) →
  exists v', 
    app (upgrade (S n) d) (inProd n vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p) v' vu.
Proof.
  intros vr ih.
  destruct (valrel_implies_OfType vr) as [[? ?] ?].
  destruct (invert_valrel_pEmulDV_inProd' vr) as (vs₁ & vs₂ & vu₁ & vu₂ & ? & ? & vr₁ & vr₂); subst.
  destruct w.
  * (* w = 0 *)
    destruct H1 as (wsPair & vpair).
    simpl in H0.
    canonUVal; crush.
    stlcCanForm.
    inversion H1; subst; clear H1.
    destruct_conjs; destruct H2 as [vx vx0].
    destruct (upgrade_reduces d H4 vx) as (vs₁' & vvs₁' & ty₁' & es₁).
    destruct (upgrade_reduces d H6 vx0) as (vs₂' & vvs₂' & ty₂' & es₂).
    exists (inProd (n + d) (S.pair vs₁' vs₂')).
    assert (forall w', w' < 0 → valrel dir w' (pEmulDV (n + d) p) vs₁' vu₁) by (intros; exfalso; Omega.omega).
    assert (forall w', w' < 0 → valrel dir w' (pEmulDV (n + d) p) vs₂' vu₂) by (intros; exfalso; Omega.omega).
    split.
    eapply upgrade_eval_inProd; trivial.
    eapply valrel_inProd; trivial; crush.
  * (* w = S w *)
    assert (wlt : w < S w) by eauto with arith.
    assert (h1 := ih w vs₁ vu₁ wlt (vr₁ w wlt)).
    assert (h2 := ih w vs₂ vu₂ wlt (vr₂ w wlt)).
    destruct h1 as (vs₁' & es₁ & vr₁').
    destruct h2 as (vs₂' & es₂ & vr₂').
    destruct (valrel_implies_Value vr₁').
    destruct (valrel_implies_Value vr₂').
    exists (inProd (n + d) (S.pair vs₁' vs₂')).
    destruct H.
    eauto using upgrade_eval_inProd, valrel_inProd'.
Qed. 

Lemma downgrade_inSum_works {n d w dir p vs vu} :
  valrel dir w (pEmulDV (S (n + d)) p) (inSum (n + d) vs) vu →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV (n + d) p) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p) vs₁' vu₁) →
  exists v', 
    app (downgrade (S n) d) (inSum (n + d) vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p) v' vu.
Proof.
  intros vr ih.
  destruct (valrel_implies_OfType vr) as [[? ?] ?].
  destruct (invert_valrel_pEmulDV_inSum' vr) as (vs' & vu' & ? & vr'); subst.
  destruct w.
  + (* w = 0 *)
    unfold repEmul in H0; canonUVal; 
    inversion H3; subst; clear H3.
    stlcCanForm;
      destruct (downgrade_reduces H6 H4) as (vs'' & vvs'' & ty' & es');
      assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p) vs'' vu') by (intros; exfalso; Omega.omega);
      [exists (inSum n (inl vs''))|exists (inSum n (inr vs''))];
      destruct H2 as [[eq1 eq2] | [eq1 eq2]];
      inversion eq1; inversion eq2; subst; clear eq1;
      destruct H1 as (closed_vu & vvu);
      (split;
       [refine (downgrade_eval_inSum _ _ _ es'); crush|
        assert (ot' : OfType (pEmulDV n p) vs'' vu') by crush;
          eapply (valrel_inSum ot'); eauto]).
    + (* w = S w *)
      assert (wlt : w < S w) by eauto with arith.
      specialize (vr' w wlt).
      destruct (ih w _ _ wlt vr') as (vs'' & es' & vr'').
      destruct (valrel_implies_Value vr'').
      destruct H2 as [[eq1 eq2] | [eq1 eq2]];
        subst;
        [exists (inSum n (S.inl vs'')) |exists (inSum n (S.inr vs''))];
        (split; [refine (downgrade_eval_inSum _ _ _ es'); crush
                | eapply (valrel_inSum' vr''); crush]).
Qed.

Lemma upgrade_inSum_works {n d w dir p vs vu} :
  valrel dir w (pEmulDV (S n) p) (inSum n vs) vu →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV n p) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p) vs₁' vu₁) →
  exists v', 
    app (upgrade (S n) d) (inSum n vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p) v' vu.
Proof.
  intros vr ih.
  destruct (valrel_implies_OfType vr) as [[? ?] ?].
  destruct (invert_valrel_pEmulDV_inSum' vr) as (vs' & vu' & ? & vr'); subst.
  destruct w.
  + (* w = 0 *)
    unfold repEmul in H0; canonUVal; 
    inversion H3; subst; clear H3.
    stlcCanForm;
      destruct (upgrade_reduces d H6 H4) as (vs'' & vvs'' & ty' & es');
      assert (forall w', w' < 0 → valrel dir w' (pEmulDV (n + d) p) vs'' vu') by (intros; exfalso; Omega.omega);
      [exists (inSum n (inl vs''))|exists (inSum n (inr vs''))];
      destruct H2 as [[eq1 eq2] | [eq1 eq2]];
      inversion eq1; inversion eq2; subst; clear eq1;
      destruct H1 as (closed_vu & value_vu);
      (split;
       [refine (upgrade_eval_inSum _ _ _ es'); crush|
        assert (ot' : OfType (pEmulDV (n + d) p) vs'' vu') by crush;
          eapply (valrel_inSum ot'); eauto]).
    + (* w = S w *)
      assert (wlt : w < S w) by eauto with arith.
      specialize (vr' w wlt).
      destruct (ih w _ _ wlt vr') as (vs'' & es' & vr'').
      destruct (valrel_implies_Value vr'').
      destruct H2 as [[eq1 eq2] | [eq1 eq2]];
        subst;
        [exists (inSum (n + d) (S.inl vs'')) |exists (inSum (n + d) (S.inr vs''))];
        (split; [refine (upgrade_eval_inSum _ _ _ es'); crush
                | eapply (valrel_inSum' vr''); crush]).
Qed.

Lemma downgrade_inArr_works {n d w dir p vs vu} :
  valrel dir w (pEmulDV (S (n + d)) p) (inArr (n + d) vs) vu →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV (n + d) p) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p) vs₁' vu₁) →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV n p) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p) vs₁' vu₁) →
  exists v', 
    app (downgrade (S n) d) (inArr (n + d) vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p) v' vu.
Proof.
  intros vr ihd ihu.
  destruct (valrel_implies_OfType vr) as [[vv ty] otu].
  exists (inArr n (abs (UVal n) (app (downgrade n d) (app (vs[wk]) (app (upgrade n d) (var 0)))))).
  split.
  - eapply downgrade_eval_inArr; crush.
  - eapply valrel_inArr.
    apply invert_valrel_pEmulDV_inArr in vr.
    simpl in vv.
    apply valrel_ptarr_inversion in vr; destruct_conjs; subst.
    simpl in *.

    (* unfold the valrel-ptarr *)
    change (abs (UVal n)) with (abs (repEmul (pEmulDV n p))).
    apply valrel_lambda; crushOfType; crushTyping;
    eauto using downgrade_T, upgrade_T.
    rewrite -> ?upgrade_sub, ?downgrade_sub.

    rewrite <- ap_liftSub; rewrite <- up_liftSub;
    rewrite -> liftSub_wkm; rewrite (apply_wkm_beta1_up_cancel vr vs).

    (* first execute the upgrade *)
    specialize (ihu w' _ _ H0 H1).
    destruct ihu as (vs' & eups & vr').
    enough (termrel dir w' (pEmulDV n p)
                    (app (downgrade n d) (app (abs (UVal (n + d)) vr) vs')) (H [beta1 vu])) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' eups _ _ _) tr'); 
            inferContext; crush; eauto using downgrade_value).

    (* now beta-reduce *)
    enough (termrel dir w' (pEmulDV n p)
                    (app (downgrade n d) (vr[beta1 vs']))
                    H[beta1 vu]) as tr'
    by (refine (termrel_antired_star_left _ tr'); simpl; eauto with eval;
        apply evalToStar;
        destruct (valrel_implies_Value vr') as [? _];
        assert (e₀ : app (abs (UVal (n + d)) vr) vs' -->₀ vr[beta1 vs']) by (eauto with eval);
        eapply (eval_from_eval₀ e₀); inferContext; crush; eauto using downgrade_value).
     
    (* now execute the application *)
    specialize (H4 w' _ _ H0 vr').
    eapply (termrel_ectx' H4); S.inferContext; U.inferContext; crush;
    eauto using downgrade_value.

    (* now execute the downgrade *)
    assert (wlt0 : w'0 < w) by Omega.omega.
    specialize (ihd w'0 _ _ wlt0 H21).
    destruct ihd as (vs'' & edowns & vr'').
    enough (termrel dir w'0 (pEmulDV n p)
                    vs'' vu0) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' edowns _ _ _) tr'); 
            inferContext; crush; eauto using downgrade_value).
    
    (* conclude *)
    apply valrel_in_termrel.
    assumption.
Qed. 

Lemma upgrade_inArr_works {n d w dir p vs vu} :
  valrel dir w (pEmulDV (S n) p) (inArr n vs) vu →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV (n + d) p) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p) vs₁' vu₁) →
  (forall w' vs₁ vu₁, w' < w →
              valrel dir w' (pEmulDV n p) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p) vs₁' vu₁) →
  exists v', 
    app (upgrade (S n) d) (inArr n vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p) v' vu.
Proof.
  intros vr ihd ihu.
  destruct (valrel_implies_OfType vr) as [[vv ty] otu].
  exists (inArr (n + d) (abs (UVal (n + d)) (app (upgrade n d) (app (vs[wk]) (app (downgrade n d) (var 0)))))).
  split.
  - eapply upgrade_eval_inArr; crush.
  - eapply valrel_inArr.
    apply invert_valrel_pEmulDV_inArr in vr.
    simpl in vv.
    apply valrel_ptarr_inversion in vr; destruct_conjs; subst.
    simpl in *.

    (* unfold the valrel-ptarr *)
    change (abs (UVal (n + d))) with (abs (repEmul (pEmulDV (n + d) p))).
    apply valrel_lambda; crushOfType; crushTyping;
    eauto using upgrade_T, downgrade_T.
    rewrite -> ?upgrade_sub, ?downgrade_sub.

    (* sigh... *)
    rewrite <- ap_liftSub; rewrite <- up_liftSub;
    rewrite -> liftSub_wkm; rewrite (apply_wkm_beta1_up_cancel vr vs).

    (* first execute the upgrade *)
    specialize (ihd w' _ _ H0 H1).
    destruct ihd as (vs' & edowns & vr').
    enough (termrel dir w' (pEmulDV (n + d) p)
                    (app (upgrade n d) (app (abs (UVal n) vr) vs')) (H [beta1 vu])) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' edowns _ _ _) tr'); 
            inferContext; crush; eauto using upgrade_value).

    (* now beta-reduce *)
    enough (termrel dir w' (pEmulDV (n + d) p)
                    (app (upgrade n d) (vr[beta1 vs']))
                    H[beta1 vu]) as tr'
    by (refine (termrel_antired_star_left _ tr');
        apply evalToStar;
        destruct (valrel_implies_Value vr') as [? _];
        assert (e₀ : app (abs (UVal n) vr) vs' -->₀ vr[beta1 vs']) by (eauto with eval);
        eapply (eval_from_eval₀ e₀); inferContext; crush; eauto using upgrade_value).
     
    (* now execute the application *)
    specialize (H4 w' _ _ H0 vr').
    eapply (termrel_ectx' H4); S.inferContext; U.inferContext; crush;
    eauto using upgrade_value.

    (* now execute the upgrade *)
    assert (wlt0 : w'0 < w) by Omega.omega.
    specialize (ihu w'0 _ _ wlt0 H21).
    destruct ihu as (vs'' & eups & vr'').
    enough (termrel dir w'0 (pEmulDV (n + d) p)
                    vs'' vu0) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' eups _ _ _) tr'); 
            inferContext; crush; eauto using upgrade_value).

    (* conclude *)
    repeat crushLRMatch.
Qed. 

Lemma downgrade_zero_works {d v vu dir w p} :
  dir_world_prec 0 w dir p →
  valrel dir w (pEmulDV d p) v vu →
  exists v', 
    app (downgrade 0 d) v -->* v' ∧
    valrel dir w (pEmulDV 0 p) v' vu.
Proof.
  intros dwp vr;
  destruct (valrel_implies_OfType vr) as [[vv ty] otu];
  exists (unkUVal 0).
  destruct (dwp_zero dwp).
  destruct otu as (closed_vu & vvu); unfold OfTypeUtlc' in vvu.
  eauto using downgrade_zero_eval, valrel_unk.
Qed.

Lemma downgrade_S_works {n d v vu dir w p} :
  dir_world_prec (S n) w dir p →
  valrel dir w (pEmulDV (S (n + d)) p) v vu →
  (forall v vu w', dir_world_prec n w' dir p → valrel dir w' (pEmulDV (n + d) p) v vu →
                   exists v', 
                     app (downgrade n d) v -->* v' ∧ valrel dir w' (pEmulDV n p) v' vu) →
  (forall v vu w', dir_world_prec n w' dir p → valrel dir w' (pEmulDV n p) v vu →
                   exists v', 
                     app (upgrade n d) v -->* v' ∧ valrel dir w' (pEmulDV (n + d) p) v' vu) →
  exists v', 
    app (downgrade (S n) d) v -->* v' ∧
    valrel dir w (pEmulDV (S n) p) v' vu.
Proof.
  intros dwp vr IHdown IHup.
  destruct (valrel_implies_Value vr);
  destruct (valrel_implies_OfType vr) as [[vv ty] [closed_vu otu]];
   unfold repEmul in ty.
  canonUVal.
  - (* unkUVal *)
    exists (unkUVal (S n)).
    change (S (n + d)) with (S n + d).
    eauto using downgrade_eval_unk, valrel_unk, invert_valrel_pEmulDV_unk.
  - (* inUnit *)
    exists (inUnit n x).
    eauto using downgrade_eval_inUnit, invert_valrel_pEmulDV_inUnit', valrel_inUnit.
  - (* inBool *)
    exists (inBool n x).
    eauto using downgrade_eval_inBool, invert_valrel_pEmulDV_inBool', valrel_inBool.
  - (* inProd *)
    eapply (downgrade_inProd_works vr); crush;
    eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
  - (* inSum *)
    eapply (downgrade_inSum_works vr); crush;
    eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
  - (* inArr *)
    eapply (downgrade_inArr_works vr); crush.
    + eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
    + eapply IHup; try assumption; eapply dwp_invert_S'; crush.
Qed.

Lemma upgrade_zero_works {d v vu dir w p} :
  dir_world_prec 0 w dir p →
  valrel dir w (pEmulDV 0 p) v vu →
  exists v', 
    app (upgrade 0 d) v -->* v' ∧
    valrel dir w (pEmulDV d p) v' vu.
Proof.
  intros dwp vr;
  destruct (valrel_implies_OfType vr) as [[vv ty] [closed_vu otu]];
  exists (unkUVal d).
  destruct (dwp_zero dwp).
  eauto using upgrade_zero_eval, valrel_unk, dwp_zero.
Qed.

Lemma upgrade_S_works {n d v vu dir w p} :
  dir_world_prec (S n) w dir p →
  valrel dir w (pEmulDV (S n) p) v vu →
  (forall v vu w', dir_world_prec n w' dir p → valrel dir w' (pEmulDV (n + d) p) v vu →
                   exists v', 
                     app (downgrade n d) v -->* v' ∧ valrel dir w' (pEmulDV n p) v' vu) →
  (forall v vu w', dir_world_prec n w' dir p → valrel dir w' (pEmulDV n p) v vu →
                   exists v', 
                     app (upgrade n d) v -->* v' ∧ valrel dir w' (pEmulDV (n + d) p) v' vu) →
  exists v', 
    app (upgrade (S n) d) v -->* v' ∧
    valrel dir w (pEmulDV (S n + d) p) v' vu.
Proof.
  change (S n + d) with (S (n + d)).
  intros dwp vr IHdown IHup.
  destruct (valrel_implies_Value vr);
  destruct (valrel_implies_OfType vr) as [[vv ty] [closed_vu otu]];
   unfold repEmul in ty.
  canonUVal.
  - (* unkUVal *)
    exists (unkUVal (S n + d)).
    eauto using upgrade_eval_unk, valrel_unk, invert_valrel_pEmulDV_unk.
  - (* inUnit *)
    exists (inUnit (n + d) x).
    eauto using upgrade_eval_inUnit, invert_valrel_pEmulDV_inUnit', valrel_inUnit.
  - (* inBool *)
    exists (inBool (n + d) x).
    eauto using upgrade_eval_inBool, invert_valrel_pEmulDV_inBool', valrel_inBool.
  - (* inProd *)
    eapply (upgrade_inProd_works vr); crush;
    eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inSum *)
    eapply (upgrade_inSum_works vr); crush;
    eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inArr *)
    eapply (upgrade_inArr_works vr); crush.
    + eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
    + eapply IHup; try assumption; eapply dwp_invert_S'; crush.
Qed.

Lemma downgrade_works {n d v vu dir w p} :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p) v vu →
  exists v', 
    app (downgrade n d) v -->* v' ∧
    valrel dir w (pEmulDV n p) v' vu
with upgrade_works {n v vu dir w p} d :
       dir_world_prec n w dir p →
       valrel dir w (pEmulDV n p) v vu →
       exists v', 
         app (upgrade n d) v -->* v' ∧
         valrel dir w (pEmulDV (n + d) p) v' vu.
Proof.
  (* the following is easier, but cheats by using the inductive hypotheses
  immediately *)
  (* auto using downgrade_zero_works, downgrade_S_works, upgrade_zero_works, upgrade_S_works. *)

  - destruct n.
    + intros; apply downgrade_zero_works; trivial.
    + specialize (downgrade_works n).
      specialize (upgrade_works n).
      auto using downgrade_S_works.
  - destruct n.
    + intros; apply upgrade_zero_works; trivial.
    + specialize (downgrade_works n).
      specialize (upgrade_works n).
      auto using upgrade_S_works.
Qed.

Lemma downgrade_works' {n d v vu dir w p} :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p) v vu →
  termrel dir w (pEmulDV n p) (app (downgrade n d) v) vu.
Proof.
  intros dwp vr.
  destruct (downgrade_works dwp vr) as (v' & es & vr').
  apply valrel_in_termrel in vr'.
  refine (termrel_antired_star_left es vr').
Qed.

Lemma downgrade_works'' {n d v vu dir w p} :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p) v vu →
  termrel₀ dir w (pEmulDV n p) (app (downgrade n d) v) vu.
Proof.
  intros dwp vr.
  destruct (downgrade_works dwp vr) as (v' & es & vr').
  apply valrel_in_termrel₀ in vr'.
  refine (termrel₀_antired_star_left es vr').
Qed.

Lemma upgrade_works' {n v vu dir w p} d :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV n p) v vu →
  termrel dir w (pEmulDV (n + d) p) (app (upgrade n d) v) vu.
Proof.
  intros dwp vr.
  destruct (upgrade_works d dwp vr) as (v' & es & vr').
  apply valrel_in_termrel in vr'.
  refine (termrel_antired_star_left es vr').
Qed.

Lemma upgrade_works'' {n v vu dir w p} d :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV n p) v vu →
  termrel₀ dir w (pEmulDV (n + d) p) (app (upgrade n d) v) vu.
Proof.
  intros dwp vr.
  destruct (upgrade_works d dwp vr) as (v' & es & vr').
  apply valrel_in_termrel₀ in vr'.
  refine (termrel₀_antired_star_left es vr').
Qed.

Lemma compat_upgrade {Γ ts dir m tu n p} d :
  dir_world_prec n m dir p →
  ⟪ Γ ⊩ ts ⟦ dir , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ app (upgrade n d) ts ⟦ dir , m ⟧ tu : pEmulDV (n + d) p ⟫.
Proof.
  intros.
  repeat crushLRMatch.
  - eauto using upgrade_T with typing.
  - crushUtlcScoping.
  - intros.
    specialize (H2 w H3 _ _ H4).
    simpl; repeat crushStlcSyntaxMatchH.
    rewrite upgrade_sub.
    eapply (termrel_ectx' H2); S.inferContext; U.inferContext; crush;
    eauto using upgrade_value.
    simpl.
    eauto using upgrade_works', dwp_mono.
Qed.

Lemma compat_downgrade {Γ ts dir m tu n p d} :
  dir_world_prec n m dir p →
  ⟪ Γ ⊩ ts ⟦ dir , m ⟧ tu : pEmulDV (n + d) p ⟫ →
  ⟪ Γ ⊩ app (downgrade n d) ts ⟦ dir , m ⟧ tu : pEmulDV n p ⟫.
Proof.
  intros.
  repeat crushLRMatch.
  - eauto using downgrade_T with typing.
  - crushUtlcScoping.
  - intros.
    specialize (H2 w H3 _ _ H4).
    simpl; repeat crushStlcSyntaxMatchH.
    rewrite downgrade_sub.
    eapply (termrel_ectx' H2); S.inferContext; U.inferContext; crush;
    eauto using downgrade_value.
    simpl.
    eauto using downgrade_works', dwp_mono.
Qed.
