Require Import UVal.UVal.
Require Import Stlc.SpecSyntax.
Require Import Stlc.Inst.
Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.PseudoType.

Require Omega.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     crushOfType;
     split;
     subst*);
  try discriminate;
  eauto with eval;
  repeat crushStlcSyntaxMatchH (* remove apTm's again *).

Fixpoint downgrade (n : nat) (d : nat) :=
  abs (UVal (n + d))
      (match n with
         | 0 => unkUVal 0
         | S n => 
           caseUVal (n + d) (var 0)
                    (unkUVal (S n))
                    (inUnit n (var 0))
                    (inBool n (var 0))
                    (inProd n 
                            (pair
                               (app (downgrade n d) (proj₁ (var 0)))
                               (app (downgrade n d) (proj₂ (var 0)))))
                    (inSum n 
                           (caseof (var 0)
                                   (inl (app (downgrade n d) (var 0)))
                                   (inr (app (downgrade n d) (var 0)))))
                    (inArr n
                           (abs (UVal n) 
                                (app (downgrade n d) 
                                     (app (var 1) 
                                          (app (upgrade n d) (var 0))))))
       end)
with 
upgrade (n : nat) (d : nat) :=
  abs (UVal n)
      (match n with
         | 0 => unkUVal d
         | S n => 
           caseUVal n (var 0)
                    (unkUVal (S n + d))
                    (inUnit (n + d) (var 0))
                    (inBool (n + d) (var 0))
                    (inProd (n + d) 
                            (pair
                               (app (upgrade n d) (proj₁ (var 0)))
                               (app (upgrade n d) (proj₂ (var 0)))))
                    (inSum (n + d) 
                           (caseof (var 0)
                                   (inl (app (upgrade n d) (var 0)))
                                   (inr (app (upgrade n d) (var 0)))))
                    (inArr (n + d)
                           (abs (UVal (n + d)) 
                                (app (upgrade n d) 
                                     (app (var 1) 
                                          (app (downgrade n d) (var 0))))))
       end).

Lemma upgrade_T {Γ n d} :
  ⟪ Γ ⊢ upgrade n d : UVal n ⇒ UVal (n + d) ⟫
with 
downgrade_T {Γ n d} :
  ⟪ Γ ⊢ downgrade n d : UVal (n + d) ⇒ UVal n ⟫.
Proof.
  (* can I combine eauto and crushTyping somehow? *)
  - induction n; unfold upgrade, downgrade;
    auto with typing uval_typing.
  - induction n; unfold upgrade, downgrade;
    auto with typing uval_typing.
Qed.
 
Lemma upgrade_closed {n d} :
  ⟨ 0 ⊢ upgrade n d ⟩.
Proof.
  enough (⟪ empty ⊢ upgrade n d : UVal n ⇒ UVal (n + d) ⟫) as ty by eapply (wt_implies_ws ty).
  eapply upgrade_T.
Qed.

Lemma downgrade_closed {n d} :
  ⟨ 0 ⊢ downgrade n d ⟩.
Proof.
  enough (⟪ empty ⊢ downgrade n d : UVal (n + d) ⇒ UVal n ⟫) as ty by eapply (wt_implies_ws ty).
  eapply downgrade_T.
Qed.

Lemma upgrade_sub {n d γ} : (upgrade n d)[γ] = upgrade n d.
Proof.
  (* Sigh why is coq not finding this instance??? *) 
(*   About wsApTm. *)
(*   apply wsClosed_invariant.  *)
(*   eapply upgrade_closed. *)
(* Qed. *)
Admitted.

Lemma downgrade_sub {n d γ} : (downgrade n d)[γ] = downgrade n d.
Proof.
Admitted.


Lemma downgrade_value {n d} : Value (downgrade n d).
Proof.
  destruct n; simpl; trivial.
Qed.

Lemma upgrade_value {n d} : Value (downgrade n d).
Proof.
  destruct n; simpl; trivial.
Qed.

Lemma downgrade_zero_eval {d v} : Value v → app (downgrade 0 d) v -->* unkUVal 0.
Proof.
  intros vv.
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  simpl; eauto with eval. 
Qed.

Lemma downgrade_eval_unk {n d} : app (downgrade n d) (unkUVal (n + d)) -->* unkUVal n.
Proof.
  assert (vv : Value (unkUVal (n + d))) by apply unkUVal_Value.
  destruct n; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval. crush.
    simpl; eauto with eval. 
  - change _ with (Value (inl unit)) in vv.
    eapply evalStepStar. eapply eval₀_to_eval. crush.
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
    eapply caseUVal_eval_unk.
Qed.

Lemma downgrade_eval_inUnit {n d v} : 
  Value v → app (downgrade (S n) d) (inUnit (n + d) v) -->* inUnit n v.
Proof.
  intros vv.
  assert (Value (inUnit (n + d) v)) by (simpl; crush).
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
  eapply evalStepTrans. eapply caseUVal_eval_unit; crush.
  simpl; crush.
Qed.
  
Lemma downgrade_eval_inBool {n d v} : 
  Value v → app (downgrade (S n) d) (inBool (n + d) v) -->* inBool n v.
Proof.
  intros vv.
  assert (Value (inBool (n + d) v)) by (simpl; crush).
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
  eapply evalStepTrans. eapply caseUVal_eval_bool; crush.
  simpl; crush.
Qed.
 
Lemma downgrade_eval_inProd {n d v₁ v₂ v₁' v₂'} : 
  Value v₁ → Value v₂ → Value v₁' → Value v₂' →
  app (downgrade n d) v₁ -->* v₁' →
  app (downgrade n d) v₂ -->* v₂' →
  app (downgrade (S n) d) (inProd (n + d) (pair v₁ v₂)) -->* inProd n (pair v₁' v₂').
Proof.
  intros vv₁ vv₂ vv₁' vv₂' es₁ es₂.
  assert (Value (inProd (n + d) (pair v₁ v₂))) by (simpl; crush).
  unfold downgrade.
  assert (Value (downgrade n d)) by apply downgrade_value.

  (* beta-reduce *)
  eapply evalStepStar. eapply eval₀_to_eval; crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush.
  rewrite -> ?upgrade_sub, ?downgrade_sub.

  (* evaluate UVal pattern match *)
  eapply evalStepTrans. eapply caseUVal_eval_prod; crush.
  (* downgrade under sub... *)
  simpl; crush.
  rewrite -> ?downgrade_sub.

  (* first projection *)
  eapply evalStepStar. 
  assert (ep₁ : proj₁ (pair v₁ v₂) -->₀ v₁) by crush.
  eapply (eval_from_eval₀ ep₁); inferContext; crush; simpl.

  (* recursive call 1 *)
  eapply evalStepTrans. eapply (evalstar_ctx' es₁); inferContext; crush.

  (* second projection *)
  eapply evalStepStar. 
  assert (ep₂ : proj₂ (pair v₁ v₂) -->₀ v₂) by crush.
  eapply (eval_from_eval₀ ep₂); inferContext; crush; simpl.

  (* recursive call 2 *)
  eapply evalStepTrans. eapply (evalstar_ctx' es₂); inferContext; crush.

  (* ... and we're done. *)
  simpl; crush.
Qed.

Lemma downgrade_eval_inSum {n d v v' va va'} : 
  Value v → Value v' → 
  (va = inl v ∧ va' = inl v') ∨ (va = inr v ∧ va' = inr v') →
  app (downgrade n d) v -->* v' →
  app (downgrade (S n) d) (inSum (n + d) va) -->* inSum n va'.
Proof.
  intros vv vv' eqs es.

  unfold downgrade.
  destruct eqs as [(? & ?)|(? & ?)]; subst;
  (* beta-reduce *)
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;

    (* evaluate UVal pattern match *)
    (eapply evalStepTrans; [eapply caseUVal_eval_sum; crush|]);
    (* downgrade under sub... *)
    simpl; crush;
    rewrite -> ?downgrade_sub;

    (* caseof *)
    [assert (ec : caseof (inl v) (inl (app (downgrade n d) (var 0))) (inr (app (downgrade n d) (var 0))) -->₀ ((inl (app (downgrade n d) (var 0))) [beta1 v])) by crush
    |assert (ec : caseof (inr v) (inl (app (downgrade n d) (var 0))) (inr (app (downgrade n d) (var 0))) -->₀ ((inr (app (downgrade n d) (var 0))) [beta1 v])) by crush
    ];
    (eapply evalStepStar;
     [eapply (eval_from_eval₀ ec); inferContext; crush|]);
    crushStlcSyntaxMatchH (* why is this needed? *);
    rewrite -> ?downgrade_sub;

    (* recursive call *)
    (eapply evalStepTrans; [eapply (evalstar_ctx' es); inferContext; crush|]);

    (* ... and we're done. *)
    simpl; crush.
Qed.

Lemma downgrade_eval_inArr {n d v} : 
  Value v →
  app (downgrade (S n) d) (inArr (n + d) v) -->* 
      inArr n (abs (UVal n) (app (downgrade n d) (app (v[wk]) (app (upgrade n d) (var 0))))).
Proof.
  intros vv.
  unfold downgrade.

  (* beta-reduce *)
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
  rewrite -> ?upgrade_sub, ?downgrade_sub.

  (* evaluate UVal pattern match *)
  (eapply evalStepTrans; [eapply caseUVal_eval_arr; crush|]);
    (* downgrade under sub... *)
    simpl; crush;
    rewrite -> ?downgrade_sub, ?upgrade_sub.

  change (wk 0) with 1; simpl.
  eauto with eval.
Qed.

Lemma downgrade_reduces {n d v} :
  ⟪ empty ⊢ v : UVal (n + d) ⟫ → Value v →
  exists v', Value v' ∧ ⟪ empty ⊢ v' : UVal n ⟫ ∧ 
             app (downgrade n d) v -->* v'.
Proof.
  revert v; induction n;
  intros v ty vv.
  - exists (unkUVal 0).
    eauto using unkUVal_Value, unkUValT, downgrade_zero_eval.
  - canonUVal. 
    + exists (unkUVal (S n)).
      change (S (n + d)) with (S n + d).
      eauto using unkUVal_Value, unkUValT, downgrade_eval_unk.
    + exists (inUnit n x).
      eauto using inUnit_Value, inUnitT, downgrade_eval_inUnit.
    + exists (inBool n x).
      eauto using inBool_Value, inBoolT, downgrade_eval_inBool.
    + stlcCanForm.
      destruct H0 as (vx0 & vx1).
      destruct (IHn _ H2 vx0) as (x0' & vx0' & ty0 & evalx0).
      destruct (IHn _ H3 vx1) as (x1' & vx1' & ty1 & evalx1).
      exists (inProd n (pair x0' x1')).
      assert (Value (pair x0' x1')) by crush.
      eauto using inProd_Value, inProd_T, downgrade_eval_inProd with typing.

    + stlcCanForm;
      [ destruct (IHn _ H2 H0) as (vf & vvf & tyf & ex);
        exists (inSum n (inl vf))
      | destruct (IHn _ H2 H0) as (vf & vvf & tyf & ex);
        exists (inSum n (inr vf))];
      repeat split;
      eauto using inSum_Value, inSum_T, downgrade_eval_inSum with typing.
    + exists (inArr n (abs (UVal n) (app (downgrade n d) (app (x[wk]) (app (upgrade n d) (var 0)))))).
      assert (Value (abs (UVal n) (app (downgrade n d) (app (x[wk]) (app (upgrade n d) (var 0)))))) by crush.
      repeat split;
      eauto using inArr_Value, downgrade_eval_inArr, inArr_T, 
            downgrade_T, upgrade_T with typing.
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

Lemma dwp_invert_S {w d p n} : dir_world_prec (S n) (S w) d p → dir_world_prec n w d p.
Proof.
  destruct 1 as [[? ?]|[? ?]]; [left|right];
  eauto with arith.
Qed.

Lemma invert_valrel_pEmulDV_unk {dir w n d p vu} :
  valrel dir w (pEmulDV (S n + d) p) (inl unit) vu →
  p = imprecise.
Proof.
  intros vr.
  rewrite valrel_fixp in vr.
  unfold valrel' in vr.
  destruct vr as [_ [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]];
    crush.
Qed.

Lemma invert_valrel_pEmulDV_inUnit {dir w n d p vs vu} :
  valrel dir w (pEmulDV (S (n + d)) p) (inUnit (n + d) vs) vu →
  vs = S.unit ∧ vu = U.unit.
Proof.
  intros vr.
  rewrite valrel_fixp in vr.
  unfold valrel' in vr.
  destruct vr as [_ [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]];
    crush; inversion H; crush.
Qed.

Lemma invert_valrel_pEmulDV_inBool {dir w n d p vs vu} :
  valrel dir w (pEmulDV (S (n + d)) p) (inBool (n + d) vs) vu →
  (vs = S.true ∧ vu = U.true) ∨ (vs = S.false ∧ vu = U.false).
Proof.
  intros vr.
  rewrite valrel_fixp in vr.
  unfold valrel' in vr.
  destruct vr as [_ [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]];
    crush.
  inversion H; destruct H0 as [[? ?]|[? ?]]; crush.
Qed.

Lemma invert_valrel_pEmulDV_inProd {dir w n d p vs vu} :
  valrel dir w (pEmulDV (S (n + d)) p) (inProd (n + d) vs) vu →
  ∃ vs₁ vs₂ vu₁ vu₂, vs = S.pair vs₁ vs₂ ∧ vu = U.pair vu₁ vu₂ ∧
             (∀ w', w' < w → valrel dir w' (pEmulDV (n + d) p) vs₁ vu₁) ∧
             (∀ w', w' < w → valrel dir w' (pEmulDV (n + d) p) vs₂ vu₂).
Proof.
  intros vr.
  rewrite valrel_fixp in vr; unfold valrel' in vr.
  destruct vr as [[[vv ty] vvu] [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]]; simpl in *; crush.
  inversion H; subst; clear H.
  assert (Value (inProd (n + d) x)) by crush.
  canonUVal; crush; clear ty. 
  inversion H1; subst; clear H1.
  stlcCanForm.
  destruct vu; unfold prod_rel in H0; simpl in H0; try contradiction.
  exists x, x1, vu1, vu2; repeat (split; auto).
Qed.

Lemma invert_valrel_pEmulDV_inSum {dir w n d p vs vu} :
  valrel dir w (pEmulDV (S (n + d)) p) (inSum (n + d) vs) vu →
  ∃ vs' vu', ((vs = S.inl vs' ∧ vu = U.inl vu') ∨ (vs = S.inr vs' ∧ vu = U.inr vu')) ∧
             (∀ w', w' < w → valrel dir w' (pEmulDV (n + d) p) vs' vu').
Proof.
  intros vr.
  rewrite valrel_fixp in vr; unfold valrel' in vr.
  destruct vr as [[[vv ty] vvu] [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]]; simpl in *; crush.
  inversion H; subst; clear H.
  assert (Value (inSum (n + d) x)) by crush.
  canonUVal; crush; clear ty. 
  inversion H1; subst; clear H1.
  stlcCanForm;
  destruct vu; unfold sum_rel in H0; simpl in H0; try contradiction;
  exists x, vu; repeat (split; auto).
Qed.

Lemma downgrade_works {n d v vu dir w p} :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p) v vu →
  exists v', 
    app (downgrade n d) v -->* v' ∧
    valrel dir w (pEmulDV n p) v' vu. 
Proof.
  revert v vu w; induction n;
  intros v vu w dwp vr;
  destruct (valrel_implies_Value vr);
  destruct (valrel_implies_OfType vr) as [[vv ty] otu];
   unfold repEmul in ty.
  - exists (unkUVal 0).
    destruct (dwp_zero dwp).
    split; eauto using downgrade_zero_eval.
    apply valrel_unk; crush.
  - canonUVal.
    + (* unkUVal *)
      exists (unkUVal (S n)).
      change (S (n + d)) with (S n + d).
      eauto using downgrade_eval_unk, valrel_unk, invert_valrel_pEmulDV_unk.
    + (* inUnit *)
      exists (inUnit n x).
      eauto using downgrade_eval_inUnit, invert_valrel_pEmulDV_inUnit, valrel_inUnit.
    + (* inBool *)
      exists (inBool n x).
      eauto using downgrade_eval_inBool, invert_valrel_pEmulDV_inBool, valrel_inBool.
    + (* inProd *)
      destruct (invert_valrel_pEmulDV_inProd vr) as (vs₁ & vs₂ & vu₁ & vu₂ & ? & ? & vr₁ & vr₂); subst.
      destruct w.
      * (* w = 0 *)
        stlcCanForm.
        inversion H1; subst; clear H1.
        destruct H2.
        destruct (downgrade_reduces H4 H1) as (vs₁' & vvs₁' & ty₁' & es₁).
        destruct (downgrade_reduces H5 H2) as (vs₂' & vvs₂' & ty₂' & es₂).
        exists (inProd n (S.pair vs₁' vs₂')).
        assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p) vs₁' vu₁) by (intros; exfalso; Omega.omega).
        assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p) vs₂' vu₂) by (intros; exfalso; Omega.omega).
        split.
        eapply downgrade_eval_inProd; trivial.
        eapply valrel_inProd; trivial; crush.
      * (* w = S w *)
        pose proof (dwp_invert_S dwp) as dwp'. 
        assert (wlt : w < S w) by eauto with arith.
        specialize (vr₁ w wlt).
        specialize (vr₂ w wlt).
        destruct (IHn _ _ w dwp' vr₁) as (vs₁' & es₁ & vr₁').
        destruct (IHn _ _ w dwp' vr₂) as (vs₂' & es₂ & vr₂').
        destruct (valrel_implies_Value vr₁').
        destruct (valrel_implies_Value vr₂').
        exists (inProd n (S.pair vs₁' vs₂')).
        destruct H2.
        eauto using downgrade_eval_inProd, valrel_inProd'.
    + (* inSum *)
      destruct (invert_valrel_pEmulDV_inSum vr) as (vs' & vu' & ? & vr'); subst.
      destruct w.
      * (* w = 0 *)
        stlcCanForm;
        destruct (downgrade_reduces H5 H2) as (vs'' & vvs'' & ty' & es');
        assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p) vs'' vu') by (intros; exfalso; Omega.omega);
        [exists (inSum n (inl vs''))|exists (inSum n (inr vs''))];
        destruct H1 as [[eq1 eq2] | [eq1 eq2]];
        inversion eq1; inversion eq2; subst; clear eq1;
        (split;
         [refine (downgrade_eval_inSum _ _ _ es'); crush|
          assert (ot' : OfType (pEmulDV n p) vs'' vu') by crush;
            eapply (valrel_inSum ot'); eauto]).
      * (* w = S w *)
        pose proof (dwp_invert_S dwp) as dwp'. 
        assert (wlt : w < S w) by eauto with arith.
        specialize (vr' w wlt).
        destruct (IHn _ _ w dwp' vr') as (vs'' & es' & vr'').
        destruct (valrel_implies_Value vr'').
        destruct H1 as [[eq1 eq2] | [eq1 eq2]];
          subst;
          [exists (inSum n (S.inl vs'')) |exists (inSum n (S.inr vs''))];
        (split; [refine (downgrade_eval_inSum _ _ _ es'); crush
                | eapply (valrel_inSum' vr''); crush]).
    + exists (inArr n (abs (UVal n) (app (downgrade n d) (app (x[wk]) (app (upgrade n d) (var 0)))))).
      split.
      * eapply downgrade_eval_inArr; crush.
      * 
      admit.
Admitted.