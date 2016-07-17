Require Export Stlc.SpecSyntax.

(** ** Evaluation *)

Fixpoint Value (t: Tm) : Prop :=
  match t with
    | abs τ t      => True
    | unit         => True
    | true         => True
    | false        => True
    | pair t₁ t₂   => Value t₁ ∧ Value t₂
    | inl t        => Value t
    | inr t        => Value t
    | var _ | app _ _ | ite _ _ _
    | proj₁ _ | proj₂ _ | caseof _ _ _
    | seq _ _ | fixt _ _ _   => False
  end.

Fixpoint ECtx (C: PCtx) : Prop :=
  match C with
    | phole            => True
    | papp₁ C t        => ECtx C
    | papp₂ t C        => Value t ∧ ECtx C
    | pite₁ C t₂ t₃    => ECtx C
    | ppair₁ C t       => ECtx C
    | ppair₂ t C       => Value t ∧ ECtx C
    | pproj₁ C         => ECtx C
    | pproj₂ C         => ECtx C
    | pinl C           => ECtx C
    | pinr C           => ECtx C
    | pcaseof₁ C t₂ t₃ => ECtx C
    | pseq₁ C t        => ECtx C
    | pfixt τ₁ τ₂ C    => ECtx C
    | pabs _ _ | pite₂ _ _ _ | pite₃ _ _ _
    | pcaseof₂ _ _ _ | pcaseof₃ _ _ _
    | pseq₂ _ _ => False
  end.

(* Inductive Value : Tm → Prop := *)
(*   | VAbs {τ t}    : Value (abs τ t) *)
(*   | VUnit         : Value (unit) *)
(*   | VTrue         : Value (true) *)
(*   | VFalse        : Value (false) *)
(*   | VPair {t₁ t₂} : Value t₁ → Value t₂ → Value (pair t₁ t₂) *)
(*   | VInj₁ {t}     : Value t → Value (inl t) *)
(*   | VInj₂ {t}     : Value t → Value (inr t). *)

(* Inductive ECtx : PCtx → Prop := *)
(*   | EHole              : ECtx (phole) *)
(*   | EApp₁ {C t}        : ECtx C → ECtx (papp₁ C t) *)
(*   | EApp₂ {t C}        : Value t → ECtx C → ECtx (papp₂ t C) *)
(*   | EIte₁ {C t₂ t₃}    : ECtx C → ECtx (pite₁ C t₂ t₃) *)
(*   | EPair₁ {C t}       : ECtx C → ECtx (ppair₁ C t) *)
(*   | EPair₂ {t C}       : Value t → ECtx C → ECtx (ppair₂ t C) *)
(*   | EProj₁ {C}         : ECtx C → ECtx (pproj₁ C) *)
(*   | EProj₂ {C}         : ECtx C → ECtx (pproj₂ C) *)
(*   | EInj₁ {C}          : ECtx C → ECtx (pinl C) *)
(*   | EInj₂ {C}          : ECtx C → ECtx (pinr C) *)
(*   | ECaseof₁ {C t₂ t₃} : ECtx C → ECtx (pcaseof₁ C t₂ t₃) *)
(*   | ESeq₁ {C t}        : ECtx C → ECtx (pseq₁ C t) *)
(*   | EFixt {τ₁ τ₂ C}    : ECtx C → ECtx (pfixt τ₁ τ₂ C). *)

(* Inductive ECtx : Set := *)
(*   | chole *)
(*   | capp₁ (ℂ: ECtx) (t: Tm) *)
(*   | capp₂ (t: Tm) (v: Value t) (ℂ: ECtx) *)
(*   | cite (ℂ: ECtx) (t₂ t₃: Tm) *)
(*   | cpair₁ (ℂ: ECtx) (t: Tm) *)
(*   | cpair₂ (t: Tm) (v: Value t) (ℂ: ECtx) *)
(*   | cproj₁ (ℂ: ECtx) *)
(*   | cproj₂ (ℂ: ECtx) *)
(*   | cinl (ℂ: ECtx) *)
(*   | cinr (ℂ: ECtx) *)
(*   | ccaseof (ℂ: ECtx) (t₂ t₃: Tm) *)
(*   | cseq (ℂ: ECtx) (t: Tm) *)
(*   | cfixt (τ₁ τ₂: Ty) (ℂ: ECtx). *)

(* Fixpoint ectx_app (ℂ: ECtx) (t': Tm) {struct ℂ} : Tm := *)
(*   match ℂ with *)
(*     | chole           => t' *)
(*     | capp₁ ℂ t       => app (ectx_app ℂ t') t *)
(*     | capp₂ t vt ℂ    => app t (ectx_app ℂ t') *)
(*     | cite ℂ t₁ t₂    => ite (ectx_app ℂ t') t₁ t₂ *)
(*     | cpair₁ ℂ t      => pair (ectx_app ℂ t') t *)
(*     | cpair₂ t v ℂ    => pair t (ectx_app ℂ t') *)
(*     | cproj₁ ℂ        => proj₁ (ectx_app ℂ t') *)
(*     | cproj₂ ℂ        => proj₂ (ectx_app ℂ t') *)
(*     | cinl ℂ          => inl (ectx_app ℂ t') *)
(*     | cinr ℂ          => inr (ectx_app ℂ t') *)
(*     | ccaseof ℂ t₁ t₂ => caseof (ectx_app ℂ t') t₁ t₂ *)
(*     | cseq ℂ t        => seq (ectx_app ℂ t') t *)
(*     | cfixt τ₁ τ₂ ℂ   => fixt τ₁ τ₂ (ectx_app ℂ t') *)
(*   end. *)

Reserved Notation "t₁ --> t₂" (at level 40).
Inductive eval : Tm → Tm → Prop :=
  | eval_ctx {C t t'} :
      t --> t' → ECtx C → pctx_app t C --> pctx_app t' C
  | eval_beta {τ₁ t₁ t₂} :
      Value t₂ →
      app (abs τ₁ t₁) t₂ --> subst0 t₂ t₁
  | eval_ite_true {t₁ t₂} :
      ite true t₁ t₂ --> t₁
  | eval_ite_false {t₁ t₂} :
      ite false t₁ t₂ --> t₂
  | eval_proj₁ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₁ (pair t₁ t₂) --> t₁
  | eval_proj₂ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₂ (pair t₁ t₂) --> t₂
  | eval_case_inl {t t₁ t₂} :
      Value t →
      caseof (inl t) t₁ t₂ --> subst0 t t₁
  | eval_case_inr {t t₁ t₂} :
      Value t →
      caseof (inr t) t₁ t₂ --> subst0 t t₂
  | eval_seq_next {t₁ t₂} :
      Value t₁ →
      seq t₁ t₂ --> t₂
  | eval_fix {τ₁ τ₂ t} :
      fixt τ₁ τ₂ (abs (tarr τ₁ τ₂) t) -->
      subst0 (abs τ₁ (app (fixt τ₁ τ₂ (abs (tarr τ₁ τ₂) t))[wkl 1] (var 0))) t
where "t₁ --> t₂" := (eval t₁ t₂).

Inductive Terminating (t : Tm) : Prop :=
  | TerminatingI : (∀ t', t --> t' → Terminating t') → Terminating t.
Notation "t ⇓" := (Terminating t) (at level 8, format "t ⇓").

(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)
