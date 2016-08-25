Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import Omega.
Require Import Db.Lemmas.
Require Utlc.Fix.

Require Import Coq.Lists.List.

Module S.
    Include Stlc.SpecSyntax.
    Include Stlc.LemmasEvaluation.
    Include Stlc.LemmasTyping.
End S.
Module U.
  Include Utlc.SpecSyntax.
  Include Utlc.Fix.
End U.

Fixpoint erase (t : S.Tm) : U.UTm :=
  match t with
    | S.abs τ t         => U.abs (erase t)
    | S.unit            => U.unit
    | S.true            => U.true
    | S.false           => U.false
    | S.pair t₁ t₂      => U.pair (erase t₁) (erase t₂)
    | S.inl t           => U.inl (erase t)
    | S.inr t           => U.inr (erase t)
    | S.var x           => U.var x
    | S.app t₁ t₂       => U.app (erase t₁) (erase t₂)
    | S.ite t₁ t₂ t₃    => U.ite (erase t₁) (erase t₂) (erase t₃)
    | S.proj₁ t₁        => U.proj₁ (erase t₁)
    | S.proj₂ t₁        => U.proj₂ (erase t₁)
    | S.caseof t₁ t₂ t₃ => U.caseof (erase t₁) (erase t₂) (erase t₃)
    | S.seq t₁ t₂       => U.seq (erase t₁) (erase t₂)
    | S.fixt _ _ t₁     => U.app U.ufix (erase t₁)
  end.

Fixpoint erase_pctx (C : S.PCtx) : U.PCtx :=
  match C with
    | S.phole => phole
    | S.pabs τ C => U.pabs (erase_pctx C)
    | S.papp₁ C t => U.papp₁ (erase_pctx C) (erase t) 
    | S.papp₂ t C => U.papp₂ (erase t) (erase_pctx C)
    | S.pite₁ C t₂ t₃ => U.pite₁ (erase_pctx C) (erase t₂) (erase t₃)
    | S.pite₂ t₁ C t₃ => U.pite₂ (erase t₁) (erase_pctx C) (erase t₃)
    | S.pite₃ t₁ t₂ C => U.pite₃ (erase t₁) (erase t₂) (erase_pctx C)
    | S.ppair₁ C t => U.ppair₁ (erase_pctx C) (erase t)
    | S.ppair₂ t C => U.ppair₂ (erase t) (erase_pctx C)
    | S.pproj₁ C => U.pproj₁ (erase_pctx C)
    | S.pproj₂ C => U.pproj₂ (erase_pctx C)
    | S.pinl C => U.pinl (erase_pctx C)
    | S.pinr C => U.pinr (erase_pctx C)
    | S.pcaseof₁ C t₂ t₃ => U.pcaseof₁ (erase_pctx C) (erase t₂) (erase t₃)
    | S.pcaseof₂ t₁ C t₃ => U.pcaseof₂ (erase t₁) (erase_pctx C) (erase t₃)
    | S.pcaseof₃ t₁ t₂ C => U.pcaseof₃ (erase t₁) (erase t₂) (erase_pctx C)
    | S.pseq₁ C t => U.pseq₁ (erase_pctx C) (erase t)
    | S.pseq₂ t C => U.pseq₂ (erase t) (erase_pctx C)
    | S.pfixt τ₁ τ₂ C => U.papp₂ U.ufix (erase_pctx C)
  end.

Lemma erase_scope (t : S.Tm) (Γ : S.Env) (τ : S.Ty) :
  ⟪ Γ ⊢ t : τ ⟫ -> ⟨ dom Γ ⊢ erase t ⟩.
Proof.
  intro wt; induction wt; crushUtlcScoping.
  apply U.ufix_ws.
Qed.

Hint Extern 4 ⟨ _ ⊢ erase ?t ⟩ =>
  match goal with
      [ H : ⟪ _ ⊢ ?t : _ ⟫ |- _ ] => refine (erase_scope _ _ _ H)
  end.

Lemma erase_pctx_scope (C : S.PCtx) (Γ₀ Γ : S.Env) (τ₀ τ : S.Ty) :
  ⟪ ⊢ C : Γ₀ , τ₀ → Γ , τ ⟫ → ⟨ ⊢ erase_pctx C : dom Γ₀ → dom Γ ⟩.
Proof.
  intro wt; induction wt; crushUtlcScoping.
  apply U.ufix_ws.
Qed.

Ltac crushOfTypeUtlcMatch :=
  match goal with
    | [ |- exists tsb tub, S.abs _ ?tsb' = S.abs _ tsb ∧ U.abs ?tub' = U.abs tub ∧ _] => (exists tsb'; exists tub'; split; intuition)
    | [ |- exists t', U.abs ?t = U.abs t' ] => (exists t; intuition)
    | [ |- exists ts₁' ts₂' tu₁' tu₂', S.pair ?ts₁ ?ts₂ = S.pair ts₁' ts₂' ∧ U.pair ?tu₁ ?tu₂ = LR.U.pair tu₁' tu₂' ∧ _ ] => (exists ts₁; exists ts₂; exists tu₁; exists tu₂)
    | [ |- (exists ts₁' tu₁', S.inl ?ts₁ = LR.S.inl ts₁' ∧ U.inl ?tu₁ = LR.U.inl tu₁' ∧ _) ∨ _ ] => (left; exists ts₁; exists tu₁)
    | [ |- _ ∨ (exists ts₁' tu₁', S.inr ?ts₁ = LR.S.inr ts₁' ∧ U.inr ?tu₁ = LR.U.inr tu₁' ∧ _) ] => (right; exists ts₁; exists tu₁)
  end.

Ltac crushLRMatch := 
  match goal with
      [ |- _ ∧ _ ] => split
    | [ |- context[ lev ]] => unfold lev
    | [ H : context[ lev ] |- _ ] => unfold lev in *
    | [ |- ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ ] => (unfold OpenLRN; split)
    | [ H : ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ |- _ ] => (unfold OpenLRN in H; destruct_conjs)
    | [ H : valrel ?d _ ?τ ?ts ?tu |- termrel ?d _ ?τ ?ts ?tu ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ (S.abs _ _) (U.abs _) ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ S.unit U.unit ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ S.false U.false ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ S.true U.true ] => apply valrel_in_termrel
    | [ H : valrel ?d ?w ?τ ?ts ?tu |- valrel ?d ?w' ?τ ?ts ?tu ] => (refine (valrel_mono _ H); try omega)
    | [ H : envrel ?d ?w ?τ ?ts ?tu |- envrel ?d ?w' ?τ ?ts ?tu ] => (refine (envrel_mono _ H); try omega)
    | [ |- envrel ?d ?w (?Γ p▻ ?τ) (?γs↑ >=> beta1 ?ts) (?γu↑ >=> beta1 ?tu) ] => refine (extend_envrel _ _)
    | [ H : valrel _ _ ?τ ?ts ?tu |- OfType ?τ ?ts ?tu ] => refine (valrel_implies_OfType H)
    | [ |- valrel _ _ _ _ _] => rewrite -> valrel_fixp in |- *; unfold valrel' in |- *
    | [ |- S.ECtx (S.pctx_cat _ _) ] => apply S.ectx_cat
    | [ |- U.ECtx (U.pctx_cat _ _) ] => apply U.ectx_cat
    | [ H: exists tub', ?tu = U.abs tub' |- U.Value ?tu ] => (destruct H as [? ?]; subst)
    | [ |- sum_rel _ _ _ _ ] => unfold sum_rel
    | [ |- prod_rel _ _ _ _ ] => unfold prod_rel
  end.
                  
Section OfType.
  Local Ltac crush :=
    repeat (try intros;
            simpl;
            intuition; 
            repeat crushOfTypeUtlcMatch;
            repeat crushUtlcScoping;
            repeat match goal with
                       [ |- _ ∧ _ ] => split
                     | [ |- OfType _ _ _ ] => unfold OfType, OfTypeStlc
                     | [ H: OfType _ _ _  |- _ ] => destruct H as [[? ?] ?]
                     | [ H: OfTypeStlc _ _  |- _ ] => destruct H as [? ?]
                   end;
            crushTyping
           ).

  Lemma OfType_unit : OfType ptunit S.unit U.unit.
  Proof.
    crush.
  Qed.

  Lemma OfType_true : OfType ptbool S.true U.true.
  Proof.
    crush.
  Qed.
  
  Lemma OfType_false : OfType ptbool S.false U.false.
  Proof.
    crush.
  Qed.

  Lemma OfType_inl {τ₁ τ₂ ts tu} :
    OfType τ₁ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inl ts) (U.inl tu).
  Proof.
    unfold OfType.
    destruct 1 as [ots otu].
    split; unfold OfTypeStlc in *; crush.
  Qed.
  
  Lemma OfType_inr {τ₁ τ₂ ts tu} :
    OfType τ₂ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inr ts) (U.inr tu).
  Proof.
    unfold OfType.
    destruct 1 as [ots otu].
    split; unfold OfTypeStlc in *; crush.
  Qed.
  
  
  Lemma OfType_pair {τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    OfType (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    crush.
  Qed.

  Lemma OfType_lambda {τ₁ τ₂ tsb tub} :
    ⟪ empty ⊢ S.abs (repEmul τ₁) tsb : repEmul τ₁ ⇒ repEmul τ₂ ⟫ →
    OfType (ptarr τ₁ τ₂) (S.abs (repEmul τ₁) tsb) (U.abs tub).
  Proof.
    crush. 
  Qed.
End OfType.

Ltac crushOfType :=
  repeat (intuition;
          repeat match goal with
              [ |- OfType ptunit S.unit U.unit ] => apply OfType_unit
            | [ |- OfType ptbool S.true U.true ] => apply OfType_true
            | [ |- OfType ptbool S.false U.false ] => apply OfType_false
            | [ |- OfType (ptsum _ _) (S.inl _) (U.inl _)] => apply OfType_inl
            | [ |- OfType (ptsum _ _) (S.inr _) (U.inr _)] => apply OfType_inr
            | [ |- OfType (ptprod _ _) (S.pair _ _) (U.pair _ _) ] => apply OfType_pair
            | [ |- OfType (ptarr _ _) (S.abs _ _) (U.abs _) ] => apply OfType_lambda
          end; 
          repeat crushOfTypeUtlcMatch;
          intuition).

Local Ltac crush :=
  cbn in * |- ;
  repeat (cbn;
          repeat crushLRMatch;
          crushOfType;
          crushTyping;
          repeat crushUtlcSyntaxMatchH;
          repeat crushUtlcScopingMatchH;
          intuition).

Section CompatibilityLemmas.
  Lemma valrel_lambda {d τ' τ ts tu w} :
    OfType (ptarr τ' τ) (S.abs (repEmul τ') ts) (U.abs tu) →
    (forall w' vs vu, w' < w → valrel d w' τ' vs vu → termrel d w' τ (ts [beta1 vs]) (tu [beta1 vu])) →
    valrel d w (ptarr τ' τ) (S.abs (repEmul τ') ts) (U.abs tu).
  Proof.
    intros ot hyp.
    rewrite -> valrel_fixp; unfold valrel'; simpl; crush.
    now apply hyp; assumption.
  Qed.

  Lemma compat_lambda {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (S.abs (repEmul τ') ts) ⟦ d , n ⟧ abs tu : ptarr τ' τ ⟫.
  Proof.
    crush.
    - eauto using wtSub_up, envrel_implies_WtSub.
    - rewrite -> ?ap_comp.
      apply H0; crush.
  Qed.

  Lemma compat_lambda_embed {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (S.abs τ' ts) ⟦ d , n ⟧ abs tu : ptarr (embed τ') τ ⟫.
  Proof.
    rewrite <- (repEmul_embed_leftinv τ') at 2.
    apply compat_lambda.
  Qed.

  Lemma compat_unit {Γ d n} :
    ⟪ Γ ⊩ S.unit ⟦ d , n ⟧ U.unit : ptunit ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_true {Γ d n} :
    ⟪ Γ ⊩ S.true ⟦ d , n ⟧ U.true : ptbool ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_false {Γ d n} :
    ⟪ Γ ⊩ S.false ⟦ d , n ⟧ U.false : ptbool ⟫.
  Proof.
    crush.
  Qed.

  Lemma valrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    valrel d w τ₁ ts₁ tu₁ →
    valrel d w τ₂ ts₂ tu₂ →
    valrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    crush.
  Qed.

  Lemma termrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    termrel d w τ₁ ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ₂ ts₂ tu₂) →
    termrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.
    change (S.pair _ _) with (S.pctx_app ts₁ (S.ppair₁ S.phole ts₂)).
    change (U.pair _ _) with (U.pctx_app tu₁ (U.ppair₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs₂ vvu₂].
    change (S.pair _ _) with (S.pctx_app ts₂ (S.ppair₂ vs S.phole)).
    change (U.pair _ _) with (U.pctx_app tu₂ (U.ppair₂ vu U.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    eauto using valrel_in_termrel, valrel_mono, valrel_pair.
  Qed. 

  Lemma compat_pair {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : τ₁ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ S.pair ts₁ ts₂ ⟦ d , n ⟧ U.pair tu₁ tu₂ : ptprod τ₁ τ₂ ⟫.
  Proof.
    crush.
    apply termrel_pair; crush.
    refine (H1 w' _ _ _ _); unfold lev in *; try omega.
    eauto using envrel_mono.
  Qed.
 
  Lemma valrel_app {d w τ₁ τ₂ vs₁ vs₂ vu₁ vu₂} :
    valrel d w (ptarr τ₁ τ₂) vs₁ vu₁ →
    valrel d w τ₁ vs₂ vu₂ →
    termrel d w τ₂ (S.app vs₁ vs₂) (U.app vu₁ vu₂).
  Proof.
    (* destruct assumptions *)
    intros vr₁ vr₂.
    rewrite -> valrel_fixp in vr₁.
    destruct vr₁ as [ot [tsb [tub [eq₁ [eq₂ bodyrel]]]]]; subst.
    destruct (valrel_implies_Value vr₂) as [vvs₂ vvu₂].

    (* beta-reduce *) 
    assert (es : S.eval (S.app (S.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂])) by
        (refine (S.eval_ctx₀ S.phole _ I); refine (S.eval_beta vvs₂)).
    assert (es1 : S.evaln (S.app (S.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂]) 1) by 
        (eauto using S.evaln; omega).
    assert (eu : forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.app (U.abs tub) vu₂) Cu) (U.pctx_app (tub [beta1 vu₂]) Cu)) by
        (intros Cu eCu; refine (U.eval_ctx₀ Cu _ eCu); refine (U.eval_beta vvu₂)).
    assert (eu1 : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.app (U.abs tub) vu₂) Cu) (U.pctx_app (tub [beta1 vu₂]) Cu) 1) by 
        (eauto using U.evaln; omega).
    destruct w; try apply termrel_zero.
    refine (termrel_antired w es1 eu1 _ _ _); unfold lev in *; simpl; try omega.

    (* use assumption for function body *)
    eapply bodyrel; try omega; eauto using valrel_mono.
  Qed.    
    

  Lemma termrel_app {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    termrel d w (ptarr τ₁ τ₂) ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ₁ ts₂ tu₂) →
    termrel d w τ₂ (S.app ts₁ ts₂) (U.app tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.
    change (S.app _ _) with (S.pctx_app ts₁ (S.papp₁ S.phole ts₂)).
    change (U.app _ _) with (U.pctx_app tu₁ (U.papp₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs vvu].
    change (S.app _ _) with (S.pctx_app ts₂ (S.papp₂ vs S.phole)).
    change (U.app _ _) with (U.pctx_app tu₂ (U.papp₂ vu U.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    replace _ with (valrel d w'0 τ₁ vs0 vu0) in H0 by eauto.
    refine (valrel_app _ H0); crush.
  Qed. 

  Lemma compat_app {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptarr τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₁ ⟫ →
    ⟪ Γ ⊩ S.app ts₁ ts₂ ⟦ d , n ⟧ U.app tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_app _ _); crush.
    refine (H1 w' _ _ _ _); unfold lev in *; try omega.
    crush.
  Qed.

  Lemma termrel_inl {d w τ₁ τ₂ ts tu} :
    termrel d w τ₁ ts tu →
    termrel d w (ptsum τ₁ τ₂) (S.inl ts) (U.inl tu).
  Proof.
    intros tr.
    change (S.inl ts) with (S.pctx_app ts (S.pinl S.phole)).
    change (U.inl tu) with (U.pctx_app tu (U.pinl U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel;
    crush. 
  Qed.
    
  Lemma compat_inl {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₁ ⟫ →
    ⟪ Γ ⊩ S.inl ts ⟦ d , n ⟧ U.inl tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inl _); crush.
  Qed.

  Lemma termrel_inr {d w τ₁ τ₂ ts tu} :
    termrel d w τ₂ ts tu →
    termrel d w (ptsum τ₁ τ₂) (S.inr ts) (U.inr tu).
  Proof.
    intros tr.
    change (S.inr ts) with (S.pctx_app ts (S.pinr S.phole)).
    change (U.inr tu) with (U.pctx_app tu (U.pinr U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel;
    crush. 
  Qed.
    
  Lemma compat_inr {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₂ ⟫ →
    ⟪ Γ ⊩ S.inr ts ⟦ d , n ⟧ U.inr tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inr _); crush.
  Qed.

  Lemma termrel_seq {d w τ ts₁ ts₂ tu₁ tu₂} :
    termrel d w ptunit ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ ts₂ tu₂) →
    termrel d w τ (S.seq ts₁ ts₂) (U.seq tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.

    (* first evaluate ts₁ and tu₁ *)
    change (S.seq _ _) with (S.pctx_app ts₁ (S.pseq₁ S.phole ts₂)).
    change (U.seq _ _) with (U.pctx_app tu₁ (U.pseq₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then reduce to ts₂ and tu₂ *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot [eq₁ eq₂]]; subst.
    assert (S.eval (S.seq S.unit ts₂) ts₂) by 
        (apply (S.eval_ctx₀ S.phole); try refine (S.eval_seq_next _); simpl; intuition).
    assert (esn : S.evaln (S.seq S.unit ts₂) ts₂ 1) by eauto using S.evaln.
    assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.seq U.unit tu₂) Cu) (U.pctx_app tu₂ Cu)) by 
        (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_seq_next _); simpl; intuition).
    assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.seq U.unit tu₂) Cu) (U.pctx_app tu₂ Cu) 1) by eauto using U.evaln.

    (* attempt at using evalMax instead of doing manual labor *)
    (* pose (e := evalMax 2 (U.seq U.unit (var 0)) nil (idm UTm · tu₂) I). *)
    (* unfold EvalMaxResult in e; cbn in e; simpl in e. *)

    refine (termrel_antired w' esn eun _ _ _); try omega.

    (* conclude *)
    apply tr₂; intuition.
  Qed. 

  Lemma compat_seq {Γ d n ts₁ tu₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptunit ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ S.seq ts₁ ts₂ ⟦ d , n ⟧ U.seq tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    apply termrel_seq; crush.
    refine (H1 w' _ _ _ _); crush. 
  Qed.
  
  Lemma termrel_proj₂ {d w τ₁ τ₂ ts tu} :
    termrel d w (ptprod τ₁ τ₂) ts tu →
    termrel d w τ₂ (S.proj₂ ts) (U.proj₂ tu).
  Proof.
    intros tr.

    (* first reduce ts and tu *)
    change (S.proj₂ _) with (S.pctx_app ts (S.pproj₂ S.phole)).
    change (U.proj₂ _) with (U.pctx_app tu (U.pproj₂ U.phole)).
    refine (termrel_ectx _ _ tr _); crush.

    (* then evaluate the projection *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot [vs₁ [vs₂ [vu₁ [vu₂ [? [? [vr₁ vr₂]]]]]]]]; subst.
    destruct (OfType_implies_Value ot) as [[vvs₁ vvs₂] [vvu₁ vvu₂]].
    assert (S.eval (S.proj₂ (S.pair vs₁ vs₂)) vs₂) by 
        (apply (S.eval_ctx₀ S.phole); try refine (S.eval_proj₂ _ _); simpl; intuition).
    assert (esn : S.evaln (S.proj₂ (S.pair vs₁ vs₂)) vs₂ 1) by eauto using S.evaln.
    assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.proj₂ (U.pair vu₁ vu₂)) Cu) (U.pctx_app vu₂ Cu)) by 
        (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_proj₂ _); simpl; intuition).
    assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.proj₂ (U.pair vu₁ vu₂)) Cu) (U.pctx_app vu₂ Cu) 1) by eauto using U.evaln.
    destruct w'; try apply termrel_zero.
    refine (termrel_antired w' esn eun _ _ _); crush.

    apply valrel_in_termrel.
    apply vr₂; crush.
  Qed. 

  Lemma compat_proj₂ {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ S.proj₂ ts ⟦ d , n ⟧ U.proj₂ tu : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_proj₂ _); crush.
  Qed.

  Lemma termrel_proj₁ {d w τ₁ τ₂ ts tu} :
    termrel d w (ptprod τ₁ τ₂) ts tu →
    termrel d w τ₁ (S.proj₁ ts) (U.proj₁ tu).
  Proof.
    intros tr.

    (* first evaluate ts and tu *)
    change (S.proj₁ _) with (S.pctx_app ts (S.pproj₁ S.phole)).
    change (U.proj₁ _) with (U.pctx_app tu (U.pproj₁ U.phole)).
    refine (termrel_ectx _ _ tr _); crush.

    (* then evaluate the projection *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot [vs₁ [vs₂ [vu₁ [vu₂ [? [? [vr₁ vr₂]]]]]]]]; subst.
    destruct (OfType_implies_Value ot) as [[vvs₁ vvs₂] [vvu₁ vvu₂]].
    assert (S.eval (S.proj₁ (S.pair vs₁ vs₂)) vs₁) by 
        (apply (S.eval_ctx₀ S.phole); try refine (S.eval_proj₁ _ _); simpl; intuition).
    assert (esn : S.evaln (S.proj₁ (S.pair vs₁ vs₂)) vs₁ 1) by eauto using S.evaln.
    assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.proj₁ (U.pair vu₁ vu₂)) Cu) (U.pctx_app vu₁ Cu)) by 
        (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_proj₁ _); simpl; intuition).
    assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.proj₁ (U.pair vu₁ vu₂)) Cu) (U.pctx_app vu₁ Cu) 1) by eauto using U.evaln.
    destruct w'; try apply termrel_zero.
    refine (termrel_antired w' esn eun _ _ _); crush.

    (* then conclude *)
    apply valrel_in_termrel.
    apply vr₁; intuition; omega.
  Qed. 

  Lemma compat_proj₁ {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ S.proj₁ ts ⟦ d , n ⟧ U.proj₁ tu : τ₁ ⟫.
  Proof.
    crush.
    refine (termrel_proj₁ _); crush.
  Qed.
    
  Lemma termrel_ite {d w τ ts₁ ts₂ ts₃ tu₁ tu₂ tu₃} :
    termrel d w ptbool ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ ts₂ tu₂) →
    (forall w', w' ≤ w → termrel d w' τ ts₃ tu₃) →
    termrel d w τ (S.ite ts₁ ts₂ ts₃) (U.ite tu₁ tu₂ tu₃).
  Proof.
    intros tr₁ tr₂ tr₃.

    (* first evaluate ts₁ and tu₁ *)
    change (S.ite _ _ _) with (S.pctx_app ts₁ (S.pite₁ S.phole ts₂ ts₃)).
    change (U.ite _ _ _) with (U.pctx_app tu₁ (U.pite₁ U.phole tu₂ tu₃)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then evaluate the if-statement *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot [[? ?]|[? ?]]]; subst; clear ot.
    - assert (S.eval (S.ite S.true ts₂ ts₃) ts₂) by 
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_ite_true _ _); simpl; intuition).
      assert (esn : S.evaln (S.ite S.true ts₂ ts₃) ts₂ 1) by eauto using S.evaln.
      assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.ite U.true tu₂ tu₃) Cu) (U.pctx_app tu₂ Cu)) by 
          (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_ite_true _ _); simpl; intuition).
      assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.ite U.true tu₂ tu₃) Cu) (U.pctx_app tu₂ Cu) 1) by eauto using U.evaln.
      refine (termrel_antired w' esn eun _ _ _); crush.
    - assert (S.eval (S.ite S.false ts₂ ts₃) ts₃) by 
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_ite_false _ _); simpl; intuition).
      assert (esn : S.evaln (S.ite S.false ts₂ ts₃) ts₃ 1) by eauto using S.evaln.
      assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.ite U.false tu₂ tu₃) Cu) (U.pctx_app tu₃ Cu)) by 
          (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_ite_false _ _); simpl; intuition).
      assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.ite U.false tu₂ tu₃) Cu) (U.pctx_app tu₃ Cu) 1) by eauto using U.evaln.
      refine (termrel_antired w' esn eun _ _ _); crush.
  Qed. 

  Lemma compat_ite {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptbool ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ S.ite ts₁ ts₂ ts₃ ⟦ d , n ⟧ U.ite tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    crush.
    apply termrel_ite; crush.
    - refine (H3 w' _ _ _ _); crush. 
    - refine (H2 w' _ _ _ _); crush. 
  Qed.

  Lemma termrel_caseof {d w τ τ₁ τ₂ ts₁ ts₂ ts₃ tu₁ tu₂ tu₃} :
    termrel d w (ptsum τ₁ τ₂) ts₁ tu₁ →
    (forall w' vs₁ vu₁, w' ≤ w → valrel d w' τ₁ vs₁ vu₁ → termrel d w' τ (ts₂ [beta1 vs₁]) (tu₂ [ beta1 vu₁])) →
    (forall w' vs₂ vu₂, w' ≤ w → valrel d w' τ₂ vs₂ vu₂ → termrel d w' τ (ts₃ [beta1 vs₂]) (tu₃ [ beta1 vu₂])) →
    termrel d w τ (S.caseof ts₁ ts₂ ts₃) (U.caseof tu₁ tu₂ tu₃).
  Proof.
    intros tr₁ tr₂ tr₃.

    (* first evaluate ts₁ and tu₁ *)
    change (S.caseof _ _ _) with (S.pctx_app ts₁ (S.pcaseof₁ S.phole ts₂ ts₃)).
    change (U.caseof _ _ _) with (U.pctx_app tu₁ (U.pcaseof₁ U.phole tu₂ tu₃)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then evaluate the caseof *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot [[vs' [vu' [? [? vr]]]]|[vs' [vu' [? [? vr]]]]]]; subst;
    destruct (OfType_implies_Value ot) as [vvs vvu]; clear ot.
    - assert (S.eval (S.caseof (S.inl vs') ts₂ ts₃) (ts₂ [beta1 vs'])) by
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_case_inl _); simpl; intuition).
      assert (esn : S.evaln (S.caseof (S.inl vs') ts₂ ts₃) (ts₂ [beta1 vs']) 1) by eauto using S.evaln.
      assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.caseof (U.inl vu') tu₂ tu₃) Cu) (U.pctx_app (tu₂ [beta1 vu']) Cu)) by 
          (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_case_inl _ _); simpl; intuition).
      assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.caseof (U.inl vu') tu₂ tu₃) Cu) (U.pctx_app (tu₂ [beta1 vu']) Cu) 1) by eauto using U.evaln.
      destruct w'; try apply termrel_zero.
      refine (termrel_antired w' esn eun _ _ _); crush.
    - assert (S.eval (S.caseof (S.inr vs') ts₂ ts₃) (ts₃ [beta1 vs'])) by
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_case_inr _); simpl; intuition).
      assert (esn : S.evaln (S.caseof (S.inr vs') ts₂ ts₃) (ts₃ [beta1 vs']) 1) by eauto using S.evaln.
      assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.caseof (U.inr vu') tu₂ tu₃) Cu) (U.pctx_app (tu₃ [beta1 vu']) Cu)) by 
          (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_case_inr _ _); simpl; intuition).
      assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.caseof (U.inr vu') tu₂ tu₃) Cu) (U.pctx_app (tu₃ [beta1 vu']) Cu) 1) by eauto using U.evaln.
      destruct w'; try apply termrel_zero.
      refine (termrel_antired w' esn eun _ _ _); crush.
  Qed. 

  Lemma compat_caseof {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ₁ τ₂ τ} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptsum τ₁ τ₂ ⟫ →
    ⟪ Γ p▻ τ₁ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ p▻ τ₂ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ S.caseof ts₁ ts₂ ts₃ ⟦ d , n ⟧ U.caseof tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    crush.
    refine (termrel_caseof _ _ _); crush;
    rewrite -> ?ap_comp.
    - refine (H3 w' _ _ _ _); crush. 
    - refine (H2 w' _ _ _ _); crush. 
  Qed.

  Lemma termrel_fix' {d w τ₁ τ₂ vs vu} :
    valrel d w (ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂)) vs vu →
    termrel d w (ptarr τ₁ τ₂) (S.fixt (repEmul τ₁) (repEmul τ₂) vs) (U.ufix₁ vu).
  Proof.
    (* well-founded induction on w *)
    revert w vs vu.
    refine (well_founded_ind 
              (well_founded_ltof World (fun w => w)) 
              (fun w => 
                 forall vs vu, 
                   valrel d w (ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂)) vs vu →
                   termrel d w (ptarr τ₁ τ₂) (S.fixt (repEmul τ₁) (repEmul τ₂) vs) (U.ufix₁ vu)) _).
    intros w indHyp vs vu.
    
    (* destruct valrel assumption *)
    intros vr.
    destruct (valrel_implies_Value vr) as [vvs vvu].
    rewrite -> valrel_fixp in vr.
    destruct vr as [ot [tsb [tub [? [? bodyrel]]]]]; subst.

    (* evaluate *)
    assert (es : S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul (ptarr τ₁ τ₂)) tsb) --> tsb [beta1 (S.abs (repEmul τ₁) (S.app (S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul τ₁ ⇒ repEmul τ₂) tsb[wkm↑])) (S.var 0)))]) by (refine (eval_ctx₀ S.phole _ _); crush).
    assert (es1 : S.evaln (S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul (ptarr τ₁ τ₂)) tsb)) (tsb [beta1 (S.abs (repEmul τ₁) (S.app (S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul τ₁ ⇒ repEmul τ₂) tsb[wkm↑])) (S.var 0)))])  1) by 
        (eauto using S.evaln; omega).
    assert (es2 : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.ufix₁ (U.abs tub)) Cu) (U.pctx_app (tub[beta1 (U.abs (U.app (U.ufix₁ (U.abs tub[wkm↑])) (U.var 0)))]) Cu) 2) by
        (intros Cu eCu; eauto using U.evaln, U.ufix₁_evaln').
    destruct w; try apply termrel_zero.
    refine (termrel_antired w es1 es2 _ _ _); unfold lev in *; simpl; try omega.
    clear es es1 es2.

    (* use the assumption about tsb and tub we extracted from vr *)
    refine (bodyrel w _ _ _ _); try omega.

    (* prove valrel for values being substituted into tsb and tub *)
    (* don't use crush cause it messes up the OfType proof for some reason *)
    rewrite -> valrel_fixp.
    unfold valrel'; simpl.
    split; [|crush].
    - (* first the OfType relation *)
      unfold OfType, OfTypeStlc, OfTypeUtlc. repeat split; [|crush].
      econstructor; fold repEmul; econstructor; [econstructor|repeat econstructor].
      change (S.abs _ tsb[wkm↑]) with ((S.abs (repEmul τ₁ ⇒ repEmul τ₂) tsb)[wkm]).
      destruct ot as [[vtsb ttsb] ttub].
      crush.
    - (* prove the termrel of the body of the abstractions *)
      refine (termrel_app _ _); [|crush].
      change (abs (tub[wkm↑][wkm↑][(beta1 tu')↑↑])) with ((abs tub)[wkm][wkm][(beta1 tu')↑]).
      change (S.abs _ _) with  ((S.abs (repEmul τ₁ ⇒ repEmul τ₂) tsb)[wkm][(beta1 ts')]).
      rewrite <- apply_wkm_comm. 
      rewrite -> ?apply_wkm_beta1_cancel.
      change (U.app _ _) with (U.ufix₁ (abs tub)).
      (* the goal is now what we set out to prove initially but in a strictly
           later world, so we can use the induction hypothesis from our
           well-founded induction on worlds *)
      refine (indHyp _ _ _ _ _); try unfold ltof; crush.
      (* why do I need to call crush again? *)
      crush.
  Qed.
  
  Lemma termrel_fix {d w τ₁ τ₂ ts tu} :
    termrel d w (ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂)) ts tu →
    termrel d w (ptarr τ₁ τ₂) (S.fixt (repEmul τ₁) (repEmul τ₂) ts) (U.app U.ufix tu).
  Proof.
    intros tr.

    (* first normalize ts and tu *)
    change (S.fixt _ _ _) with (S.pctx_app ts (S.pfixt (repEmul τ₁) (repEmul τ₂) S.phole)).
    change (U.app _ _) with (U.pctx_app tu (U.papp₂ U.ufix U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    destruct (valrel_implies_Value H) as [vvs vvu].

    (* next, reduce (U.app U.ufix tu) by one step in the conclusion *)
    assert (es1 : S.evaln (S.fixt (repEmul τ₁) (repEmul τ₂) vs) (S.fixt (repEmul τ₁) (repEmul τ₂) vs) 0) by
        (eauto using S.evaln).
    assert (es2 : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.app U.ufix vu) Cu) (U.pctx_app (U.ufix₁ vu) Cu) 1) 
      by (intros Cu eCu; eauto using U.evaln, U.ufix_eval₁').
    refine (termrel_antired w' es1 es2 _ _ _); unfold lev in *; simpl; try omega. 

    (* then defer to valrel_fix *) 
    apply termrel_fix'; crush.
  Qed.
    
    
  Lemma compat_fix {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂) ⟫ →
    ⟪ Γ ⊩ S.fixt (repEmul τ₁) (repEmul τ₂) ts ⟦ d , n ⟧ U.app U.ufix tu : ptarr τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_fix _); crush.
  Qed.

  Lemma compat_fix' {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) ⟫ →
    ⟪ Γ ⊩ S.fixt τ₁ τ₂ ts ⟦ d , n ⟧ U.app U.ufix tu : ptarr (embed τ₁) (embed τ₂) ⟫.
  Proof.
    intros tr.
    rewrite <- (repEmul_embed_leftinv τ₁) at 1.
    rewrite <- (repEmul_embed_leftinv τ₂) at 1.
    apply compat_fix; assumption.
  Qed.

  Lemma erase_correct {Γ d n ts τ} :
    ⟪ Γ ⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ erase ts : embed τ ⟫.
  Proof.
    induction 1; simpl; eauto using compat_inl, compat_inr, compat_pair, compat_lambda_embed, compat_app, compat_false, compat_true, compat_var, compat_unit, embedCtx_works, compat_seq, compat_ite, compat_proj₁, compat_proj₂, compat_caseof, compat_fix'.
  Qed. 

End CompatibilityLemmas.