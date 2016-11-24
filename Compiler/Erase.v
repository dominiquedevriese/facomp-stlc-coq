Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import Omega.
Require Import Db.Lemmas.
Require Import Utlc.Fix.

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

Local Ltac crush :=
  cbn in * |- ;
  repeat
    (cbn;
     repeat crushLRMatch;
     crushOfType;
     crushTyping;
     repeat crushRepEmulEmbed;
     repeat crushUtlcSyntaxMatchH;
     repeat crushUtlcScopingMatchH;
     subst;
     trivial
    ); try omega; eauto.

Section CompatibilityLemmas.

  Lemma compat_lambda {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (S.abs (repEmul τ') ts) ⟦ d , n ⟧ U.abs tu : ptarr τ' τ ⟫.
  Proof.
    crush.
    - eauto using wsSub_up, envrel_implies_WsSub, wsAp.
    - eauto using wtSub_up, envrel_implies_WtSub.
    - rewrite -> ?ap_comp.
      apply H1; crush.
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

  Lemma compat_pair {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : τ₁ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ S.pair ts₁ ts₂ ⟦ d , n ⟧ U.pair tu₁ tu₂ : ptprod τ₁ τ₂ ⟫.
  Proof.
    crush.
    apply termrel_pair; crush.
    refine (H2 w' _ _ _ _); unfold lev in *; try omega.
    eauto using envrel_mono.
  Qed.

  Lemma compat_app {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptarr τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₁ ⟫ →
    ⟪ Γ ⊩ S.app ts₁ ts₂ ⟦ d , n ⟧ U.app tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_app _ _); crush.
    refine (H2 w' _ _ _ _); unfold lev in *; try omega.
    crush.
  Qed.

  Lemma compat_inl {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₁ ⟫ →
    ⟪ Γ ⊩ S.inl ts ⟦ d , n ⟧ U.inl tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inl _); crush.
  Qed.

  Lemma compat_inr {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₂ ⟫ →
    ⟪ Γ ⊩ S.inr ts ⟦ d , n ⟧ U.inr tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inr _); crush.
  Qed.

  Lemma compat_seq {Γ d n ts₁ tu₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptunit ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ S.seq ts₁ ts₂ ⟦ d , n ⟧ U.seq tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    apply termrel_seq; crush.
    refine (H2 w' _ _ _ _); crush.
  Qed.

  Lemma compat_proj₂ {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ S.proj₂ ts ⟦ d , n ⟧ U.proj₂ tu : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_proj₂ _); crush.
  Qed.

  Lemma compat_proj₁ {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ S.proj₁ ts ⟦ d , n ⟧ U.proj₁ tu : τ₁ ⟫.
  Proof.
    crush.
    refine (termrel_proj₁ _); crush.
  Qed.

  Lemma compat_ite {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptbool ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ S.ite ts₁ ts₂ ts₃ ⟦ d , n ⟧ U.ite tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    crush.
    apply termrel_ite; crush.
    - refine (H5 w' _ _ _ _); crush.
    - refine (H3 w' _ _ _ _); crush.
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
    - refine (H5 w' _ _ _ _); crush.
    - refine (H3 w' _ _ _ _); crush.
  Qed.

  Lemma compat_fix {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂) ⟫ →
    ⟪ Γ ⊩ S.fixt (repEmul τ₁) (repEmul τ₂) ts ⟦ d , n ⟧ U.app U.ufix tu : ptarr τ₁ τ₂ ⟫.
  Proof.
    crush.
    - eapply ufix_ws.
    - refine (termrel_fix _); crush.
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

  Lemma erase_ctx_correct {Γ Γ' d n C τ τ'} :
    ⟪ ⊢ C : Γ , τ → Γ' , τ'⟫ →
    ⟪ ⊩ C ⟦ d , n ⟧ erase_pctx C : embedCtx Γ , embed τ → embedCtx Γ' , embed τ' ⟫.
  Proof.
    intros ty; unfold OpenLRCtxN; split; [crush|idtac].
    induction ty; simpl; 
    intros ts tu lr;
      try assumption; (* deal with phole *)
      repeat match goal with
               | [ H : ⟪ _ ⊢ _ : _ ⟫ |- _ ] => eapply erase_correct in H
             end;
      specialize (IHty ts tu lr);
      eauto using compat_inl, compat_inr, compat_pair, compat_lambda_embed, compat_app, compat_false, compat_true, compat_var, compat_unit, embedCtx_works, compat_seq, compat_ite, compat_proj₁, compat_proj₂, compat_caseof, compat_fix'.
  Qed. 

End CompatibilityLemmas.