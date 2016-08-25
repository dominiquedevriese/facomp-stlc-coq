Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecScoping.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.Inst.
Require Import Utlc.DecideEqual.

Require Import Coq.Relations.Relation_Operators.
Require Coq.Lists.List.
Module L := Coq.Lists.List.

Local Ltac crush :=
  intros;
  repeat
    (cbn in *;
     eauto with eval;
     repeat crushDbSyntaxMatchH;
     repeat crushUtlcSyntaxMatchH;
     repeat crushUtlcEvaluationMatchH;
     (* repeat crushDbLemmasMatchH; *)
     repeat crushDbLemmasRewriteH;
     try subst);
  try discriminate;
  eauto.

Inductive VarInfo : Set :=
| vi_Value
| vi_Unknown.

Inductive ctxeval : UTm → UTm → Set :=
| mkCtxEval : forall Cu t₀ t₀', ECtx Cu → t₀ -->₀ t₀' → ctxeval (pctx_app t₀ Cu) (pctx_app t₀' Cu).

Lemma ctxeval_eval {t t'} : ctxeval t t' → t --> t'.
Proof.
  destruct 1.
  refine (eval_ctx₀ _ _ _); crush.
Qed.

Lemma ctxeval_eval_ctx {t t'} : ctxeval t t' → forall Cu, ECtx Cu → pctx_app t Cu --> pctx_app t' Cu.
Proof.
  destruct 1; crush; rewrite <- ?pctx_cat_app; eauto using ectx_cat with eval.
Qed.


Lemma extend_ctxeval tu tu' Cu : ECtx Cu → ctxeval tu tu' → ctxeval (pctx_app tu Cu) (pctx_app tu' Cu).
Proof.
  intros eCu ce. 
  induction ce.
  rewrite <- ?pctx_cat_app.
  eauto using ctxeval, ectx_cat.
Qed.

Inductive EvalStep γ : UTm → Set :=
| IntermediateStep : forall t t', ctxeval (t [γ]) (t' [γ]) → EvalStep γ t
| CrashStep : forall Cu, ECtx (Cu [ γ ]) → EvalStep γ (pctx_app wrong Cu)
| TerminationStep : forall (vu : UTm), Value (vu [ γ ]) → EvalStep γ vu
| NeutralStep : forall tu, EvalStep γ tu.

Lemma stepEval_app_vals γ tu₁ tu₂ (vu₁ : Value (tu₁ [γ])) (vu₂ : Value (tu₂ [γ])) : EvalStep γ (app tu₁ tu₂).
Proof.
  destruct tu₁; crush;
  try match goal with
    | [ |- EvalStep γ (app (abs _) _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ ((tu₁ [beta1 tu₂])[γ]) I _);
       rewrite -> apply_beta1_comm;
       eapply eval_beta; crush)
    | [ |- EvalStep γ (app (var _) _) ] => 
      eapply NeutralStep
    | [ |- EvalStep γ (app _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ (wrong [γ]) I _);
       eapply eval_beta_wrong)
  end; crush.
Defined.

Definition stepEval_app {tu₁ tu₂ γ} (e₁ : EvalStep γ tu₁) (e₂ : EvalStep γ tu₂) : EvalStep γ (app tu₁ tu₂) :=
  match e₁ in EvalStep _ tu₁ return (EvalStep γ (app tu₁ tu₂)) with
    | NeutralStep _ tu₁  => NeutralStep _ (app tu₁ tu₂)
    | CrashStep _ Cu eCu => CrashStep _ (papp₁ Cu tu₂) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep γ (app tu₁ tu₂) (app tu₁' tu₂)  (extend_ctxeval _ _ (papp₁ phole (tu₂ [γ])) I e)
    | TerminationStep _ vu₁ vvu₁ => 
      match e₂ with
        | NeutralStep _ tu₂ => NeutralStep _ (app vu₁ tu₂)
        | CrashStep _ Cu eCu => CrashStep _ (papp₂ vu₁ Cu) (conj vvu₁ eCu)
        | IntermediateStep _ tu₂ tu₂' e =>
          IntermediateStep _ (app vu₁ tu₂) (app vu₁ tu₂') (extend_ctxeval tu₂[γ] tu₂'[γ] (papp₂ vu₁[γ] phole) (conj vvu₁ I) e)
        | TerminationStep _ vu₂ vvu₂ => stepEval_app_vals _ vu₁ vu₂ vvu₁ vvu₂
      end
  end.

Lemma stepEval_ite_val tu₁ {γ tu₂ tu₃} (vu₁ : Value tu₁[γ]) : EvalStep γ (ite tu₁ tu₂ tu₃).
Proof.
  destruct tu₁; crush;
  try match goal with
    | [ |- EvalStep _ (ite true _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ _ I _);
       eapply eval_ite_true)
    | [ |- EvalStep _ (ite false _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ _ I _);
       eapply eval_ite_false)
    | [ |- EvalStep _ (ite (var _) _ _) ] => 
      eapply NeutralStep
    | [ |- EvalStep _ (ite _ _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ (wrong [γ]) I _);
       eapply eval_ite_wrong)
  end; crush.
Defined.

Definition stepEval_ite {γ tu₁ tu₂ tu₃} (e₁ : EvalStep γ tu₁) : EvalStep γ (ite tu₁ tu₂ tu₃) :=
  match e₁ with
    | NeutralStep _ tu₁  => NeutralStep _ (ite tu₁ tu₂ tu₃)
    | CrashStep _ Cu eCu => CrashStep _ (pite₁ Cu _ _) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (ite tu₁ tu₂ tu₃) (ite tu₁' tu₂ tu₃) (extend_ctxeval tu₁[γ] tu₁'[γ] (pite₁ phole tu₂[γ] tu₃[γ]) I e)
    | TerminationStep _ vu₁ vvu₁ => stepEval_ite_val vu₁ vvu₁
  end.

Lemma stepEval_caseof_val tu₁ {γ tu₂ tu₃} (vu₁ : Value tu₁[γ]) : EvalStep γ (caseof tu₁ tu₂ tu₃).
Proof.
  destruct tu₁; crush;
  match goal with
    | [ |- EvalStep _ (caseof (inl ?tu₁) _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ (tu₂[beta1 tu₁][γ]) I _);
       rewrite -> apply_beta1_comm;
       eapply eval_case_inl)
    | [ |- EvalStep _ (caseof (inr ?tu₁) _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ (tu₃[beta1 tu₁][γ]) I _);
       rewrite -> apply_beta1_comm;
       eapply eval_case_inr)
    | [ |- EvalStep _ (caseof (var _) _ _) ] => 
      eapply NeutralStep
    | [ |- EvalStep _ (caseof _ _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ wrong[γ] I _);
       eapply eval_case_wrong)
  end; crush.
Defined.

Definition stepEval_caseof {γ tu₁ tu₂ tu₃} (e₁ : EvalStep γ tu₁) : EvalStep γ (caseof tu₁ tu₂ tu₃) :=
  match e₁ with
    | NeutralStep _ tu₁  => NeutralStep _ (caseof tu₁ tu₂ tu₃)
    | CrashStep _ Cu eCu => CrashStep _ (pcaseof₁ Cu tu₂ tu₃) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (caseof tu₁ tu₂ tu₃) (caseof tu₁' tu₂ tu₃) (extend_ctxeval tu₁[γ] tu₁'[γ] (pcaseof₁ phole tu₂[γ↑] tu₃[γ↑]) I e)
    | TerminationStep _ vu₁ vvu₁ => stepEval_caseof_val vu₁ vvu₁
  end.


Definition stepEval_pair {γ tu₁ tu₂} (e₁ : EvalStep γ tu₁) (e₂ : EvalStep γ tu₂) : EvalStep γ (pair tu₁ tu₂) :=
  match e₁ in EvalStep _ tu₁ return EvalStep γ (pair tu₁ tu₂) with
    | NeutralStep _ tu₁  => NeutralStep _ (pair tu₁ tu₂)
    | CrashStep _ Cu eCu => CrashStep _ (ppair₁ Cu _) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (pair tu₁ tu₂) (pair tu₁' tu₂) (extend_ctxeval _ _ (ppair₁ phole tu₂[γ]) I e)
    | TerminationStep _ vu₁ vvu₁ => 
      match e₂ in EvalStep _ tu₂ return EvalStep γ (pair vu₁ tu₂) with
        | NeutralStep _ tu₂ => NeutralStep _ (pair vu₁ tu₂)
        | CrashStep _ Cu eCu => CrashStep _ (ppair₂ _ Cu) (conj vvu₁ eCu)
        | IntermediateStep _ tu₂ tu₂' e =>
          IntermediateStep _ (pair vu₁ tu₂) (pair vu₁ tu₂') (extend_ctxeval _ _ (ppair₂ vu₁[γ] phole) (conj vvu₁ I) e)
        | TerminationStep _ vu₂ vvu₂ => TerminationStep _ (pair vu₁ vu₂) (conj vvu₁ vvu₂)
      end
  end.

Lemma stepEval_proj₁_val γ tu₁ (vu₁ : Value tu₁[γ]) : EvalStep γ (proj₁ tu₁).
Proof.
  destruct tu₁; crush;
  match goal with
    | [ |- EvalStep _ (proj₁ (pair _ _)) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ _ I _);
       eapply eval_proj₁)
    | [ |- EvalStep _ (proj₁ (var _)) ] => 
      eapply NeutralStep 
    | [ |- EvalStep _ (proj₁ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ (wrong [γ]) I _);
       eapply eval_proj₁_wrong)
  end; crush.
Defined.

Definition stepEval_proj₁ {γ tu₁} (e₁ : EvalStep γ tu₁) : EvalStep γ (proj₁ tu₁) :=
  match e₁ with
    | NeutralStep _ tu₁  => NeutralStep _ (proj₁ tu₁)
    | CrashStep _ Cu eCu => CrashStep _ (pproj₁ Cu) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (proj₁ tu₁) (proj₁ tu₁') (extend_ctxeval _ _ (pproj₁ phole) I e)
    | TerminationStep _ vu₁ vvu₁ => stepEval_proj₁_val _ vu₁ vvu₁
  end.

Lemma stepEval_proj₂_val γ tu₁ (vu₁ : Value tu₁[γ]) : EvalStep γ (proj₂ tu₁).
Proof.
  destruct tu₁; crush;
  match goal with
    | [ |- EvalStep _ (proj₂ (pair _ _)) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ _ I _);
       eapply eval_proj₂)
    | [ |- EvalStep _ (proj₂ (var _)) ] => 
      eapply NeutralStep
    | [ |- EvalStep _ (proj₂ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ wrong[γ] I _);
       eapply eval_proj₂_wrong)
  end; crush.
Defined.

Definition stepEval_proj₂ {γ tu₁} (e₁ : EvalStep γ tu₁) : EvalStep γ (proj₂ tu₁) :=
  match e₁ with
    | NeutralStep _ tu₁  => NeutralStep _ (proj₂ tu₁)
    | CrashStep _ Cu eCu => CrashStep _ (pproj₂ Cu) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (proj₂ tu₁) (proj₂ tu₁') (extend_ctxeval _ _ (pproj₂ phole) I e)
    | TerminationStep _ vu₁ vvu₁ => stepEval_proj₂_val _ vu₁ vvu₁
  end.

Definition stepEval_inl {γ tu₁} (e₁ : EvalStep γ tu₁) : EvalStep γ (inl tu₁) :=
  match e₁ with
    | NeutralStep _ tu₁  => NeutralStep _ (inl tu₁)
    | CrashStep _ Cu eCu => CrashStep _ (pinl Cu) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (inl tu₁) (inl tu₁') (extend_ctxeval _ _ (pinl phole) I e)
    | TerminationStep _ vu₁ vvu₁ => TerminationStep _ (inl vu₁) vvu₁
  end.

Definition stepEval_inr {γ tu₁} (e₁ : EvalStep γ tu₁) : EvalStep γ (inr tu₁) :=
  match e₁ with
    | NeutralStep _ tu₁  => NeutralStep _ (inr tu₁)
    | CrashStep _ Cu eCu => CrashStep _ (pinr Cu) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (inr tu₁) (inr tu₁') (extend_ctxeval _ _ (pinr phole) I e)
    | TerminationStep _ vu₁ vvu₁ => TerminationStep _ (inr vu₁) vvu₁
  end.

Lemma stepEval_seq_val tu₁ {γ tu₂} (vu₁ : Value tu₁[γ]) : EvalStep γ (seq tu₁ tu₂).
Proof.
  destruct tu₁; crush;
  match goal with
    | [ |- EvalStep _ (seq unit _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ _ I _);
       eapply eval_seq_next)
    | [ |- EvalStep _ (seq (var _) _) ] => 
      eapply NeutralStep
    | [ |- EvalStep _ (seq _ _) ] => 
      (eapply IntermediateStep;
       refine (mkCtxEval phole _ wrong[γ] I _);
       eapply eval_seq_wrong)
  end; crush.
Defined.

Definition stepEval_seq {γ tu₁ tu₂} (e₁ : EvalStep γ tu₁) : EvalStep γ (seq tu₁ tu₂) :=
  match e₁ with
    | NeutralStep _ tu₁  => NeutralStep _ (seq tu₁ tu₂)
    | CrashStep _ Cu eCu => CrashStep _ (pseq₁ Cu tu₂) eCu
    | IntermediateStep _ tu₁ tu₁' e => 
      IntermediateStep _ (seq tu₁ tu₂) (seq tu₁' tu₂) (extend_ctxeval _ _ (pseq₁ phole tu₂[γ]) I e)
    | TerminationStep _ vu₁ vvu₁ => stepEval_seq_val vu₁ vvu₁
  end.

Definition varInfoTm (vi : VarInfo) (t : UTm) : Prop :=
  match vi with
    | vi_Value => Value t
    | vi_Unknown => True
  end.

Fixpoint varInfoSub (varInfo : list VarInfo) (γ : Sub UTm) :=
  match varInfo with
      nil => True
    | cons vi vis => varInfoTm vi (γ 0) ∧ varInfoSub vis (fun x => γ (S x))
  end.

Definition stepEval_varInfo γ vi t : varInfoTm vi (t[γ]) → EvalStep γ t :=
  match vi return varInfoTm vi t[γ] → EvalStep _ t with
    | vi_Value => fun vit => TerminationStep _ _ vit
    | vi_Unknown => fun _ => NeutralStep _ t
  end.
 


Fixpoint stepEval_var' i varInfo γ inc : varInfoSub varInfo (fun x => γ (inc x)) → EvalStep γ (var (inc i)) :=
  match varInfo return varInfoSub varInfo (fun x => γ (inc x)) → EvalStep γ (var (inc i)) with
    | nil => (* variable i is out of range of the info in vis *)
      fun _ => NeutralStep γ (var (inc i))
    | cons vi varInfo => 
      match i return varInfoSub (cons vi varInfo) (fun x => γ (inc x)) → EvalStep γ (var (inc i)) with
        | 0 => fun vis => stepEval_varInfo γ vi (var (inc 0)) (proj1 vis)
        | S i => fun vis => stepEval_var' i varInfo γ (fun x => inc (S x)) (proj2 vis)
      end
  end.

Definition stepEval_var i varInfo γ : varInfoSub varInfo γ  → EvalStep γ (var i) :=
  stepEval_var' i varInfo γ (fun x => x).

Lemma stepEval (tu : UTm) varInfo γ : (varInfoSub varInfo γ) → EvalStep γ tu.
Proof.
  intros vis.
  induction tu; simpl;
  repeat match goal with
    | [ |- EvalStep _ wrong ] => apply (CrashStep _ phole)
    | [ |- EvalStep _ (var ?i) ] => refine (stepEval_var i varInfo γ vis)
    | [ |- EvalStep _ (abs _) ] => apply TerminationStep
    | [ |- EvalStep _ (app _ _) ] => apply stepEval_app
    | [ |- EvalStep _ wrong ] => apply (CrashStep phole)
    | [ |- EvalStep _ unit ] => apply TerminationStep
    | [ |- EvalStep _ true ] => apply TerminationStep
    | [ |- EvalStep _ false ] => apply TerminationStep
    | [ |- EvalStep _ (ite _ _ _) ] => apply stepEval_ite
    | [ |- EvalStep _ (caseof _ _ _) ] => apply stepEval_caseof
    | [ |- EvalStep _ (pair _ _) ] => apply stepEval_pair
    | [ |- EvalStep _ (seq _ _) ] => apply stepEval_seq
    | [ |- EvalStep _ (proj₁ _) ] => apply stepEval_proj₁
    | [ |- EvalStep _ (proj₂ _) ] => apply stepEval_proj₂
    | [ |- EvalStep _ (inl _) ] => apply stepEval_inl
    | [ |- EvalStep _ (inr _) ] => apply stepEval_inr
  end; crush.
Defined.

Definition evalStep_source {γ} : sigT (EvalStep γ) → UTm :=
  fun ses =>
    match ses with
      | existT _ t es => t
    end.

Definition evalStep_result {γ}: sigT (EvalStep γ) → UTm :=
  fun ses =>
    match ses with
        | existT _ _ es =>
          match es with
            | CrashStep _ _ _ => wrong
            | IntermediateStep _ _ t' _ => t'
            | TerminationStep _ tu _ => tu
            | NeutralStep _ tu => tu
          end
    end.

Definition continueEval (n : nat) γ {tu} (es : EvalStep γ tu) (ind : forall ut, list (sigT (EvalStep γ))) varInfo :
  (varInfoSub varInfo γ) → list (sigT (EvalStep γ)) :=
       fun vis => 
         match es with
           | IntermediateStep _ t t' e => cons (existT (EvalStep γ) t (IntermediateStep γ t t' e)) (ind t')
           | CrashStep _ Cu eCu => cons (existT (EvalStep _) _ (CrashStep _ Cu eCu)) nil
           | TerminationStep _ vu vvu => cons (existT (EvalStep _) _ (TerminationStep _ vu vvu)) nil
           | NeutralStep _ tu => cons (existT (EvalStep _) _ (NeutralStep _ tu)) nil
         end.

Fixpoint boundedEval (n : nat) (tu : UTm) varInfo γ : (varInfoSub varInfo γ) → list (sigT (EvalStep γ)) :=
  fun vis =>
  match n with
    | 0 => nil
    | S n => continueEval n γ (stepEval tu varInfo γ vis) (fun t' => boundedEval n t' varInfo γ vis) varInfo vis
  end.

Lemma decide_pctx_phole Cu : Cu = phole ∨ Cu ≠ phole.
Proof.
  induction Cu; 
  match goal with
    | [ |- phole = phole ∨ phole ≠ phole] => left
    | [ |- _ ] => right
  end; crush.
Qed.

Lemma evalStar_ctx_wrong₀ Cu : ECtx Cu → pctx_app wrong Cu -->* wrong.
Proof.
  destruct (decide_pctx_phole Cu); subst; eauto with eval.
Qed.

Lemma continueEval_sound n γ (es : sigT (EvalStep γ)) es' t' varInfo vis ind :
  (forall t'' es', L.In es' (ind t'') → evalStep_result es' = t' → t''[γ] -->* t'[γ]) →
  L.In es' (continueEval n γ (projT2 es) ind varInfo vis) → evalStep_result es' = t' → (evalStep_source es)[γ] -->* t'[γ].
Proof.
  intros indHyp el eq.
  destruct es as [? [?|?|?|?]]; crush; 
  destruct el; subst; try contradiction;
  eauto using ctxeval_eval with eval.
  rewrite -> pctx_app_sub.
  eauto using evalStar_ctx_wrong₀.
Qed.

Lemma boundedEval_sound n t varInfo γ vis es t' : 
  L.In es (boundedEval n t varInfo γ vis) → evalStep_result es = t' → t [γ] -->* t'[γ].
Proof.
  revert t es.
  induction n; try contradiction.
  intros t es.
  refine (continueEval_sound n γ (existT (EvalStep γ) _ (stepEval t varInfo γ vis)) es t' varInfo vis _ _).
  eauto using IHn.
Qed.

Lemma continueEval_sound_ctx n γ (es : sigT (EvalStep γ)) es' t' varInfo vis ind :
  (forall t'' es', L.In es' (ind t'') → evalStep_source es' = t' → forall Cu, ECtx Cu → pctx_app t''[γ] Cu -->* pctx_app t'[γ] Cu) →
  L.In es' (continueEval n γ (projT2 es) ind varInfo vis) → evalStep_source es' = t' → 
  forall Cu, ECtx Cu → pctx_app ((evalStep_source es)[γ]) Cu -->* pctx_app (t'[γ]) Cu.
Proof.
  intros indHyp el eq.
  destruct es as [? [?|?|?|?]]; crush; 
  destruct el; subst; try contradiction;
  eauto using ctxeval_eval_ctx, indHyp, evalStar_ctx_wrong₀ with eval.
Qed.

Lemma boundedEval_sound_ctx n t t' varInfo γ vis es : 
  L.In es (boundedEval n t varInfo γ vis) → 
  evalStep_source es = t' → 
  forall Cu, ECtx Cu → pctx_app (t [γ]) Cu -->* pctx_app (t'[γ]) Cu.
Proof.
  revert t es.
  induction n; try contradiction.
  intros t es.
  refine (continueEval_sound_ctx n γ (existT (EvalStep γ) _ (stepEval t varInfo γ vis)) es t' varInfo vis _ _).
  eauto using IHn.
Qed.

Lemma findReduct_source {γ} t (steps : list (sigT (EvalStep γ))) : option (exists es, L.In es steps ∧ evalStep_source es = t).
Proof.
  induction steps; [apply None|].
  destruct (decide_eq_UTm t (evalStep_source a)).
  - apply Some; exists a; crush.
  - destruct IHsteps; [apply Some|apply None].
    destruct e as [es [el eq]].
    exists es; crush.
Defined.

Lemma findReduct_result {γ} t (steps : list (sigT (EvalStep γ))) : option (exists es, L.In es steps ∧ evalStep_result es = t).
Proof.
  induction steps; [apply None|].
  destruct (decide_eq_UTm t (evalStep_result a)).
  - apply Some; exists a; crush.
  - destruct IHsteps; [apply Some|apply None].
    destruct e as [es [el eq]].
    exists es; crush.
Qed.

Fixpoint findLast {A} (l : list A) : option A :=
  match l with
      nil => None
    | cons es nil => Some es
    | cons _ l => findLast l
  end.

Definition IfSome {A} (r : option A) (P : A → Type) : Type :=
  match r with
      None => True
    | Some e => P e
  end.

Lemma IfSome_map {A P P'} {o : option A} : (forall x, P x → P' x) → IfSome o P → IfSome o P'.
Proof.
  destruct o; crush.
Defined.

Lemma findLast_works {A} (l : list A) : IfSome (findLast l) (fun x => L.In x l).
Proof.
  induction l; simpl; auto.
  destruct l; crush.
  refine (IfSome_map _ IHl); crush.
Defined.

Definition EvalMaxResultH {γ} (t : UTm) (es : option (sigT (EvalStep γ))) : Type :=
  match es with
      None => True
    | Some es => forall t', evalStep_source es = t' → forall Cu, ECtx Cu → pctx_app t[γ] Cu -->* pctx_app t'[γ] Cu
  end.

Definition EvalMaxResult n t varInfo γ vis :=
  IfSome (findLast (boundedEval n t varInfo γ vis))
         (fun es => forall Cu, ECtx Cu → pctx_app t[γ] Cu -->* pctx_app (evalStep_source es)[γ] Cu).

Definition evalMax n t varInfo γ vis : EvalMaxResult n t varInfo γ vis.
Proof.
  unfold EvalMaxResult.
  refine (IfSome_map _ (findLast_works (boundedEval n t varInfo γ vis))).
  intros x el.
  eapply boundedEval_sound_ctx; crush.
Qed.