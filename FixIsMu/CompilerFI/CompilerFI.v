(* Require Import StlcFix.SpecScoping. *)
(* Require Import StlcFix.LemmasScoping. *)
(* Require Import StlcFix.DecideEval. *)
Require Import LogRelFI.PseudoTypeFI.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LRFI.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import Lia.
Require Import Db.Lemmas.

Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.CanForm.
Require Import StlcFix.SpecEquivalent.

Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.CanForm.
Require Import StlcIso.SpecEquivalent.

Module F.
  Include StlcFix.SpecEvaluation.
  Include StlcFix.SpecSyntax.
  Include StlcFix.SpecTyping.
  Include StlcFix.LemmasTyping.
  Include StlcFix.LemmasEvaluation.
  Include StlcFix.CanForm.
End F.

Module I.
  Include StlcIso.SpecEvaluation.
  Include StlcIso.SpecSyntax.
  Include StlcIso.SpecTyping.
  Include StlcIso.LemmasTyping.
  Include StlcIso.LemmasEvaluation.
  Include StlcIso.CanForm.
  Include StlcIso.Fix.
End I.

Fixpoint compfi_ty (τ : F.Ty) : I.Ty :=
  match τ with
    | F.tunit => I.tunit
    | F.tarr τ1 τ2 => I.tarr (compfi_ty τ1) (compfi_ty τ2)
    | F.tsum τ1 τ2 => I.tsum (compfi_ty τ1) (compfi_ty τ2)
  end.

Fixpoint compfi_env (Γ : F.Env) : I.Env :=
  match Γ with
    | F.empty => I.empty
    | F.evar Γ τ => I.evar (compfi_env Γ) (compfi_ty τ)
  end.

Fixpoint compfi (t : F.Tm) : I.Tm :=
  match t with
    | F.var x => I.var x
    | F.abs τ t => I.abs (compfi_ty τ) (compfi t)
    | F.app t1 t2 => I.app (compfi t1) (compfi t2)
    | F.unit => I.unit
    | F.inl t => I.inl (compfi t)
    | F.inr t => I.inr (compfi t)
    | F.caseof t1 t2 t3 => I.caseof (compfi t1) (compfi t2) (compfi t3)
    | F.fixt τ1 τ2 t => I.app (I.ufix (compfi_ty τ1) (compfi_ty τ2)) (compfi t)
  end.

Fixpoint compfi_pctx (C : F.PCtx) : I.PCtx :=
  match C with
  | F.phole => I.phole
  | F.pabs τ C => I.pabs (compfi_ty τ) (compfi_pctx C)
  | F.papp₁ C t => I.papp₁ (compfi_pctx C) (compfi t)
  | F.papp₂ t C => I.papp₂ (compfi t) (compfi_pctx C)
  | F.pinl C => I.pinl (compfi_pctx C)
  | F.pinr C => I.pinr (compfi_pctx C)
  | F.pcaseof₁ C t₂ t₃ => I.pcaseof₁ (compfi_pctx C) (compfi t₂) (compfi t₃)
  | F.pcaseof₂ t₁ C t₃ => I.pcaseof₂ (compfi t₁) (compfi_pctx C) (compfi t₃)
  | F.pcaseof₃ t₁ t₂ C => I.pcaseof₃ (compfi t₁) (compfi t₂) (compfi_pctx C)
  | F.pfixt τ₁ τ₂ C => I.papp₂ (I.ufix (compfi_ty τ₁) (compfi_ty τ₂)) (compfi_pctx C)
  end.


Lemma smoke_test_compiler :
  (compfi F.unit) = I.unit.
Proof.
  simpl. reflexivity.
Qed.

Lemma compfi_getevar_works {i τ Γ} :
  ⟪ i : τ ∈ Γ ⟫ →
  ⟪ i : compfi_ty τ i∈ compfi_env Γ ⟫.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma compfi_typing_works {Γ t τ} :
  ⟪ Γ ⊢ t : τ ⟫ →
  ⟪ compfi_env Γ i⊢ compfi t : compfi_ty τ ⟫.
Proof.
  induction 1; F.crushTyping; I.crushTyping.
  - apply compfi_getevar_works; assumption.
  - repeat constructor; apply I.ufix₁_typing; repeat constructor.
Qed.

Lemma compfi_pctx_works {C Γ Γ' τ τ'} :
  ⟪ ⊢ C : Γ, τ → Γ', τ' ⟫ →
  ⟪ i⊢ compfi_pctx C : compfi_env Γ, compfi_ty τ →
  compfi_env Γ', compfi_ty τ' ⟫.
Proof.
  induction 1; I.crushTyping;
  try exact (compfi_typing_works H);
  try exact (compfi_typing_works H0);
  try exact (compfi_typing_works H1);
  apply I.ufix_typing.
Qed.

Lemma compileCtx_works {Γ i τ} :
  F.GetEvar Γ i τ →
  ⟪ i : embed τ p∈ embedCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvarP.
Qed.

(* Fixpoint erase (t : S.Tm) : U.UTm := *)
(*   match t with *)
(*     | S.abs τ t         => U.abs (erase t) *)
(*     | S.unit            => U.unit *)
(*     | S.true            => U.true *)
(*     | S.false           => U.false *)
(*     | S.pair t₁ t₂      => U.pair (erase t₁) (erase t₂) *)
(*     | S.inl t           => U.inl (erase t) *)
(*     | S.inr t           => U.inr (erase t) *)
(*     | S.var x           => U.var x *)
(*     | S.app t₁ t₂       => U.app (erase t₁) (erase t₂) *)
(*     | S.ite t₁ t₂ t₃    => U.ite (erase t₁) (erase t₂) (erase t₃) *)
(*     | S.proj₁ t₁        => U.proj₁ (erase t₁) *)
(*     | S.proj₂ t₁        => U.proj₂ (erase t₁) *)
(*     | S.caseof t₁ t₂ t₃ => U.caseof (erase t₁) (erase t₂) (erase t₃) *)
(*     | S.seq t₁ t₂       => U.seq (erase t₁) (erase t₂) *)
(*     | S.fixt _ _ t₁     => U.app U.ufix (erase t₁) *)
(*   end. *)

(* Fixpoint erase_pctx (C : S.PCtx) : U.PCtx := *)
(*   match C with *)
(*     | S.phole => phole *)
(*     | S.pabs τ C => U.pabs (erase_pctx C) *)
(*     | S.papp₁ C t => U.papp₁ (erase_pctx C) (erase t)  *)
(*     | S.papp₂ t C => U.papp₂ (erase t) (erase_pctx C) *)
(*     | S.pite₁ C t₂ t₃ => U.pite₁ (erase_pctx C) (erase t₂) (erase t₃) *)
(*     | S.pite₂ t₁ C t₃ => U.pite₂ (erase t₁) (erase_pctx C) (erase t₃) *)
(*     | S.pite₃ t₁ t₂ C => U.pite₃ (erase t₁) (erase t₂) (erase_pctx C) *)
(*     | S.ppair₁ C t => U.ppair₁ (erase_pctx C) (erase t) *)
(*     | S.ppair₂ t C => U.ppair₂ (erase t) (erase_pctx C) *)
(*     | S.pproj₁ C => U.pproj₁ (erase_pctx C) *)
(*     | S.pproj₂ C => U.pproj₂ (erase_pctx C) *)
(*     | S.pinl C => U.pinl (erase_pctx C) *)
(*     | S.pinr C => U.pinr (erase_pctx C) *)
(*     | S.pcaseof₁ C t₂ t₃ => U.pcaseof₁ (erase_pctx C) (erase t₂) (erase t₃) *)
(*     | S.pcaseof₂ t₁ C t₃ => U.pcaseof₂ (erase t₁) (erase_pctx C) (erase t₃) *)
(*     | S.pcaseof₃ t₁ t₂ C => U.pcaseof₃ (erase t₁) (erase t₂) (erase_pctx C) *)
(*     | S.pseq₁ C t => U.pseq₁ (erase_pctx C) (erase t) *)
(*     | S.pseq₂ t C => U.pseq₂ (erase t) (erase_pctx C) *)
(*     | S.pfixt τ₁ τ₂ C => U.papp₂ U.ufix (erase_pctx C) *)
(*   end. *)

(* Lemma erase_scope (t : S.Tm) (Γ : S.Env) (τ : S.Ty) : *)
(*   ⟪ Γ ⊢ t : τ ⟫ -> ⟨ dom Γ ⊢ erase t ⟩. *)
(* Proof. *)
(*   intro wt; induction wt; crushUtlcScoping. *)
(*   apply U.ufix_ws. *)
(* Qed. *)

(* Hint Extern 4 ⟨ _ ⊢ erase ?t ⟩ => *)
(*   match goal with *)
(*       [ H : ⟪ _ ⊢ ?t : _ ⟫ |- _ ] => refine (erase_scope _ _ _ H) *)
(*   end. *)

(* Lemma erase_pctx_scope (C : S.PCtx) (Γ₀ Γ : S.Env) (τ₀ τ : S.Ty) : *)
(*   ⟪ ⊢ C : Γ₀ , τ₀ → Γ , τ ⟫ → ⟨ ⊢ erase_pctx C : dom Γ₀ → dom Γ ⟩. *)
(* Proof. *)
(*   intro wt; induction wt; crushUtlcScoping. *)
(*   apply U.ufix_ws. *)
(* Qed. *)

Local Ltac crush :=
  cbn in * |- ;
  repeat
    (cbn;
     repeat crushLRMatch;
     crushOfType;
     F.crushTyping;
     I.crushTyping;
     repeat crushRepEmulEmbed;
     repeat F.crushStlcSyntaxMatchH;
     repeat I.crushStlcSyntaxMatchH;
     subst;
     trivial
    ); try lia; eauto.

Lemma compiler_is_fxToIs_embed :
  ∀ τ : F.Ty, compfi_ty τ = fxToIs (embed τ).
Proof.
  induction τ; simpl;
    try rewrite IHτ1; try rewrite IHτ2;
      reflexivity.
Qed.

Lemma compiler_is_fxToIs_embed_env :
  ∀ Γ : F.Env, compfi_env Γ = fxToIsCtx (embedCtx Γ).
Proof.
  induction Γ; crush; apply compiler_is_fxToIs_embed.
Qed.

Section CompatibilityLemmas.

  Lemma compat_lambda {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs (repEmul τ') ts) ⟦ d , n ⟧ (I.abs (fxToIs τ') tu) : ptarr τ' τ ⟫.
  Proof.
    crush.
    - eauto using I.wtSub_up, envrel_implies_WtSub_iso.
    - eauto using F.wtSub_up, envrel_implies_WtSub.
    - rewrite -> ?ap_comp.
      apply H1; crush.
  Qed.

  Lemma compat_lambda_embed {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs τ' ts) ⟦ d , n ⟧ (I.abs (fxToIs (embed τ')) tu) : ptarr (embed τ') τ ⟫.
  Proof.
    rewrite <- (repEmul_embed_leftinv τ') at 2.
    apply compat_lambda.
  Qed.

  Lemma compat_lambda_embed' {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs τ' ts) ⟦ d , n ⟧ (I.abs (compfi_ty τ') tu) : ptarr (embed τ') τ ⟫.
  Proof.
    rewrite (compiler_is_fxToIs_embed τ').
    apply compat_lambda_embed.
  Qed.

  Lemma compat_unit {Γ d n} :
    ⟪ Γ ⊩ F.unit ⟦ d , n ⟧ I.unit : ptunit ⟫.
  Proof.
    crush.
  Qed.

(*   Lemma compat_true {Γ d n} : *)
(*     ⟪ Γ ⊩ S.true ⟦ d , n ⟧ U.true : ptbool ⟫. *)
(*   Proof. *)
(*     crush. *)
(*   Qed. *)

(*   Lemma compat_false {Γ d n} : *)
(*     ⟪ Γ ⊩ S.false ⟦ d , n ⟧ U.false : ptbool ⟫. *)
(*   Proof. *)
(*     crush. *)
(*   Qed. *)

(*   Lemma compat_pair {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} : *)
(*     ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : τ₁ ⟫ → *)
(*     ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ → *)
(*     ⟪ Γ ⊩ S.pair ts₁ ts₂ ⟦ d , n ⟧ U.pair tu₁ tu₂ : ptprod τ₁ τ₂ ⟫. *)
(*   Proof. *)
(*     crush. *)
(*     apply termrel_pair; crush. *)
(*     refine (H2 w' _ _ _ _); unfold lev in *; try omega. *)
(*     eauto using envrel_mono. *)
(*   Qed. *)

  Lemma compat_app {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptarr τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₁ ⟫ →
    ⟪ Γ ⊩ F.app ts₁ ts₂ ⟦ d , n ⟧ I.app tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_app _ _); crush.
    refine (H2 w' _ _ _ _); unfold lev in *; try lia.
    crush.
  Qed.

  Lemma compat_inl {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₁ ⟫ →
    ⟪ Γ ⊩ F.inl ts ⟦ d , n ⟧ I.inl tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inl _); crush.
  Qed.

  Lemma compat_inr {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₂ ⟫ →
    ⟪ Γ ⊩ F.inr ts ⟦ d , n ⟧ I.inr tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inr _); crush.
  Qed.

(*   Lemma compat_seq {Γ d n ts₁ tu₁ ts₂ tu₂ τ₂} : *)
(*     ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptunit ⟫ → *)
(*     ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ → *)
(*     ⟪ Γ ⊩ S.seq ts₁ ts₂ ⟦ d , n ⟧ U.seq tu₁ tu₂ : τ₂ ⟫. *)
(*   Proof. *)
(*     crush. *)
(*     apply termrel_seq; crush. *)
(*     refine (H2 w' _ _ _ _); crush. *)
(*   Qed. *)

(*   Lemma compat_proj₂ {Γ d n ts tu τ₁ τ₂} : *)
(*     ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ → *)
(*     ⟪ Γ ⊩ S.proj₂ ts ⟦ d , n ⟧ U.proj₂ tu : τ₂ ⟫. *)
(*   Proof. *)
(*     crush. *)
(*     refine (termrel_proj₂ _); crush. *)
(*   Qed. *)

(*   Lemma compat_proj₁ {Γ d n ts tu τ₁ τ₂} : *)
(*     ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ → *)
(*     ⟪ Γ ⊩ S.proj₁ ts ⟦ d , n ⟧ U.proj₁ tu : τ₁ ⟫. *)
(*   Proof. *)
(*     crush. *)
(*     refine (termrel_proj₁ _); crush. *)
(*   Qed. *)

(*   Lemma compat_ite {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ} : *)
(*     ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptbool ⟫ → *)
(*     ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ → *)
(*     ⟪ Γ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ → *)
(*     ⟪ Γ ⊩ S.ite ts₁ ts₂ ts₃ ⟦ d , n ⟧ U.ite tu₁ tu₂ tu₃ : τ ⟫. *)
(*   Proof. *)
(*     crush. *)
(*     apply termrel_ite; crush. *)
(*     - refine (H5 w' _ _ _ _); crush. *)
(*     - refine (H3 w' _ _ _ _); crush. *)
(*   Qed. *)

  Lemma compat_caseof {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ₁ τ₂ τ} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptsum τ₁ τ₂ ⟫ →
    ⟪ Γ p▻ τ₁ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ p▻ τ₂ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ F.caseof ts₁ ts₂ ts₃ ⟦ d , n ⟧ I.caseof tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    crush.
    refine (termrel_caseof _ _ _); crush;
    rewrite -> ?ap_comp.
    - refine (H5 w' _ _ _ _); crush.
    - refine (H3 w' _ _ _ _); crush.
  Qed.

  Lemma compat_fix {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂) ⟫ →
    ⟪ Γ ⊩ F.fixt (repEmul τ₁) (repEmul τ₂) ts ⟦ d , n ⟧ I.app (I.ufix (fxToIs τ₁) (fxToIs τ₂)) tu : ptarr τ₁ τ₂ ⟫.
  Proof.
    crush.
    - eapply I.ufix_typing.
    - refine (termrel_fix _); crush.
  Qed.

  Lemma compat_fix' {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed (F.tarr (F.tarr τ₁ τ₂) (F.tarr τ₁ τ₂)) ⟫ →
    ⟪ Γ ⊩ F.fixt τ₁ τ₂ ts ⟦ d , n ⟧ I.app (I.ufix (compfi_ty τ₁) (compfi_ty τ₂)) tu : ptarr (embed τ₁) (embed τ₂) ⟫.
  Proof.
    intros tr.
    rewrite <- (repEmul_embed_leftinv τ₁) at 1.
    rewrite <- (repEmul_embed_leftinv τ₂) at 1.
    rewrite (compiler_is_fxToIs_embed τ₁) at 1.
    rewrite (compiler_is_fxToIs_embed τ₂) at 1.
    apply compat_fix; assumption.
  Qed.

  Lemma compat_fix'' {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed (F.tarr (F.tarr τ₁ τ₂) (F.tarr τ₁ τ₂)) ⟫ →
    ⟪ Γ ⊩ F.fixt τ₁ τ₂ ts ⟦ d , n ⟧ I.app (I.ufix (fxToIs (embed τ₁)) (fxToIs (embed τ₂))) tu : ptarr (embed τ₁) (embed τ₂) ⟫.
  Proof.
    rewrite <- (compiler_is_fxToIs_embed τ₁) at 1.
    rewrite <- (compiler_is_fxToIs_embed τ₂) at 1.
    exact compat_fix'.
  Qed.

  Lemma compfi_correct {Γ d n ts τ} :
    ⟪ Γ ⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ compfi ts : embed τ ⟫.
  Proof.
    induction 1; simpl; try rewrite (compiler_is_fxToIs_embed τ₁); try rewrite (compiler_is_fxToIs_embed τ₂); eauto using compat_inl, compat_inr, (* compat_pair, *) compat_lambda_embed, compat_app, (* compat_false, compat_true, *) compat_var, compat_unit, embedCtx_works, (* compat_seq, compat_ite, compat_proj₁, compat_proj₂, *) compat_caseof, compat_fix''.
  Qed.

  Lemma compfi_ctx_correct {Γ Γ' d n C τ τ'} :
    ⟪ ⊢ C : Γ , τ → Γ' , τ'⟫ →
    ⟪ ⊩ C ⟦ d , n ⟧ compfi_pctx C : embedCtx Γ , embed τ → embedCtx Γ' , embed τ' ⟫.
  Proof.
    intros ty; unfold OpenLRCtxN; split; [crush|split]; [crush|idtac].
    rewrite <- (compiler_is_fxToIs_embed τ);
    rewrite <- (compiler_is_fxToIs_embed τ');
    rewrite <- (compiler_is_fxToIs_embed_env Γ);
    rewrite <- (compiler_is_fxToIs_embed_env Γ').
    exact (compfi_pctx_works ty).
    induction ty; simpl;
    intros ts tu lr;
      try assumption; (* deal with phole *)
      repeat match goal with
               | [ H : ⟪ _ ⊢ _ : _ ⟫ |- _ ] => eapply compfi_correct in H
             end;
      specialize (IHty ts tu lr);
      eauto using compat_inl, compat_inr, (* compat_pair, *) compat_lambda_embed', compat_app, (* compat_false, compat_true, *) compat_var, compat_unit, embedCtx_works, (* compat_seq, compat_ite, compat_proj₁, compat_proj₂, *) compat_caseof, compat_fix'.
  Qed.

End CompatibilityLemmas.

Lemma equivalenceReflection {Γ t₁ t₂ τ} :
  ⟪ Γ ⊢ t₁ : τ ⟫ →
  ⟪ Γ ⊢ t₂ : τ ⟫ →
  ⟪ compfi_env Γ i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫ →
  ⟪ Γ ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂} τ,
            ⟪ Γ ⊢ t₁ : τ ⟫ →
            ⟪ Γ ⊢ t₂ : τ ⟫ →
            ⟪ compfi_env Γ i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫ →
            ∀ C τ', ⟪ ⊢ C : Γ , τ → F.empty, τ' ⟫ →
                    F.Terminating (F.pctx_app t₁ C) → F.Terminating (F.pctx_app t₂ C)) as Hltor
  by (intros t₁ t₂ τ ty1 ty2 eq C τ';
      assert (⟪ compfi_env Γ i⊢ compfi t₂ ≃ compfi t₁ : compfi_ty τ ⟫)
        by (apply I.pctx_equiv_symm; assumption);
  split;
  refine (Hltor _ _ τ _ _ _ C τ' _); assumption).

  intros t₁ t₂ τ ty1 ty2 eq C τ' tyC term.

  destruct (F.Terminating_TerminatingN term) as [n termN]; clear term.

  assert (⟪ embedCtx Γ ⊩ t₁ ⟦ dir_lt , S n ⟧ compfi t₁ : embed τ ⟫) as lrt₁ by exact (compfi_correct ty1).

  assert (⟪ ⊩ C ⟦ dir_lt , S n ⟧ compfi_pctx C : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_lt
      by apply (compfi_ctx_correct tyC).

  apply lrC_lt in lrt₁.

  assert (I.Terminating (I.pctx_app (compfi t₁) (compfi_pctx C)))
    as termu₁ by (apply (adequacy_lt lrt₁ termN); lia).

  assert (I.Terminating (I.pctx_app (compfi t₂) (compfi_pctx C))).
  eapply eq; try assumption;
  apply (compfi_pctx_works tyC).

  destruct (I.Terminating_TerminatingN H) as [n' termN']; clear H.

  assert (⟪ ⊩ C ⟦ dir_gt , S n' ⟧ compfi_pctx C : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_gt
    by (apply (compfi_ctx_correct tyC)).

  assert (⟪ embedCtx Γ ⊩ t₂ ⟦ dir_gt , S n' ⟧ compfi t₂ : embed τ ⟫) as lrt₂ by exact (compfi_correct ty2).

  apply lrC_gt in lrt₂.

  apply (adequacy_gt lrt₂ termN'); lia.
Qed.

Lemma equivalenceReflectionEmpty {t₁ t₂ τ} :
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  apply @equivalenceReflection.
Qed.
