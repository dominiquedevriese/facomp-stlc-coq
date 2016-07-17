Require Export Coq.Unicode.Utf8.

(** * Basic definitions

    This Section contains basic definitions for the de Bruijn representation
    of the abstract syntax.  *)

(** ** Domains *)

(** [Dom] is the representation of domains of typing contexts
    or of simultaneous renamings/substitutions. For the de
    Bruijn representation with a single sort with variables,
    we can represent domains as natural numbers. *)
Definition Dom : Set := nat.

Fixpoint dunion (δ₁ δ₂ : Dom) {struct δ₂} : Dom :=
  match δ₂ with
    | O    => δ₁
    | S δ₂ => S (dunion δ₁ δ₂)
  end.
Notation "δ₁ ∪ δ₂" := (dunion δ₁ δ₂) (at level 55, left associativity).

(** ** De Bruijn indices. *)
Definition Ix : Set := nat.

Reserved Notation "γ ∋ i" (at level 80).
Inductive wsIx : Dom → Ix → Prop :=
  | ws0 γ   :         S γ ∋ 0
  | wsS γ i : γ ∋ i → S γ ∋ S i
where "γ ∋ i" := (wsIx γ i).

(* Structure of (Γ ∋ i → (Γ,Δ) ∋ i), aka plus, raise. *)
Fixpoint wkl (δ: Dom) (i: Ix) {struct δ} : Ix :=
  match δ with
    | O   => i
    | S δ => S (wkl δ i)
  end.

(* Structure of (Δ ∋ i → (Γ,Δ) ∋ i), aka id, inject. *)
Fixpoint wkr (γ: Dom) (i: Ix) {struct i} : Ix :=
  match i with
    | O    => O
    | S i  => S (wkr γ i)
  end.

(* Only simplify when fully applied. *)
Arguments wkl !δ i /.
Arguments wkr γ !i /.

(** ** Simply typed terms. *)
Inductive Ty : Set :=
  | tarr (τ₁ τ₂: Ty)
  | tunit
  | tbool
  | tprod (τ₁ τ₂: Ty)
  | tsum (τ₁ τ₂: Ty).

Inductive Tm : Set :=
  | var (i: Ix)
  | abs (τ: Ty) (t: Tm)
  | app (t₁ t₂: Tm)
  | unit
  | true
  | false
  | ite (t₁ t₂ t₃: Tm)
  | pair (t₁ t₂: Tm)
  | proj₁ (t: Tm)
  | proj₂ (t: Tm)
  | inl (t: Tm)
  | inr (t: Tm)
  | caseof (t₁ t₂ t₃: Tm)
  | seq (t₁ t₂: Tm)
  | fixt (τ₁ τ₂: Ty) (t: Tm).

(* Well-scoping predicate. *)
Reserved Notation "⟨  γ ⊢ t  ⟩"
  (at level 0, γ at level 10, t at level 10).
Inductive wsTm (γ: Dom) : Tm → Prop :=
  | WsVar {i}           : γ ∋ i → ⟨ γ ⊢ var i ⟩
  | WsAbs {τ t}         : ⟨ S γ ⊢ t ⟩ → ⟨ γ ⊢ abs τ t ⟩
  | WsApp {t₁ t₂}       : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ app t₁ t₂ ⟩
  | WsUnit              : ⟨ γ ⊢ unit ⟩
  | WsTrue              : ⟨ γ ⊢ true ⟩
  | WsFalse             : ⟨ γ ⊢ false ⟩
  | WsIte {t₁ t₂ t₃}    : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ →
                          ⟨ γ ⊢ t₃ ⟩ → ⟨ γ ⊢ ite t₁ t₂ t₃ ⟩
  | WsProj1 {t}         : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ proj₁ t ⟩
  | WsProj2 {t}         : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ proj₂ t ⟩
  | WsPair {t₁ t₂}      : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ pair t₁ t₂ ⟩
  | WsInj₁ {t}          : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ inl t ⟩
  | WsInj₂ {t}          : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ inr t ⟩
  | WsCaseof {t₁ t₂ t₃} : ⟨ γ ⊢ t₁ ⟩ → ⟨ S γ ⊢ t₂ ⟩ →
                          ⟨ S γ ⊢ t₃ ⟩ → ⟨ γ ⊢ caseof t₁ t₂ t₃ ⟩
  | WsSeq {t₁ t₂}       : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ seq t₁ t₂ ⟩
  | WsFixt {τ₁ τ₂ t}    : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ fixt τ₁ τ₂ t ⟩
where "⟨  γ ⊢ t  ⟩" := (wsTm γ t).


(** ** Program contexts *)

Inductive PCtx : Set :=
  | phole
  | pabs (T: Ty) (C: PCtx)
  | papp₁ (C: PCtx) (t: Tm)
  | papp₂ (t: Tm) (C: PCtx)
  | pite₁ (C: PCtx) (t₂ t₃: Tm)
  | pite₂ (t₁: Tm) (C: PCtx) (t₃: Tm)
  | pite₃ (t₁ t₂: Tm) (C: PCtx)
  | ppair₁ (C: PCtx) (t: Tm)
  | ppair₂ (t: Tm) (C: PCtx)
  | pproj₁ (C: PCtx)
  | pproj₂ (C: PCtx)
  | pinl (C: PCtx)
  | pinr (C: PCtx)
  | pcaseof₁ (C: PCtx) (t₂ t₃: Tm)
  | pcaseof₂ (t₁: Tm) (C: PCtx) (t₃: Tm)
  | pcaseof₃ (t₁ t₂: Tm) (C: PCtx)
  | pseq₁ (C: PCtx) (t: Tm)
  | pseq₂ (t: Tm) (C: PCtx)
  | pfixt (τ₁ τ₂: Ty) (C: PCtx).

Fixpoint pctx_app (t₀: Tm) (C: PCtx) {struct C} : Tm :=
  match C with
    | phole            => t₀
    | pabs T C         => abs T (pctx_app t₀ C)
    | papp₁ C t        => app (pctx_app t₀ C) t
    | papp₂ t C        => app t (pctx_app t₀ C)
    | pite₁ C t₂ t₃    => ite (pctx_app t₀ C) t₂ t₃
    | pite₂ t₁ C t₃    => ite t₁ (pctx_app t₀ C) t₃
    | pite₃ t₁ t₂ C    => ite t₁ t₂ (pctx_app t₀ C)
    | ppair₁ C t       => pair (pctx_app t₀ C) t
    | ppair₂ t C       => pair t (pctx_app t₀ C)
    | pproj₁ C         => proj₁ (pctx_app t₀ C)
    | pproj₂ C         => proj₂ (pctx_app t₀ C)
    | pinl C           => inl (pctx_app t₀ C)
    | pinr C           => inr (pctx_app t₀ C)
    | pcaseof₁ C t₁ t₂ => caseof (pctx_app t₀ C) t₁ t₂
    | pcaseof₂ t₁ C t₂ => caseof t₁ (pctx_app t₀ C) t₂
    | pcaseof₃ t₁ t₂ C => caseof t₁ t₂ (pctx_app t₀ C)
    | pseq₁ C t        => seq (pctx_app t₀ C) t
    | pseq₂ t C        => seq t (pctx_app t₀ C)
    | pfixt τ₁ τ₂ C    => fixt τ₁ τ₂ (pctx_app t₀ C)
  end.

Fixpoint pctx_cat (C₀ C: PCtx) {struct C} : PCtx :=
  match C with
    | phole            => C₀
    | pabs T C         => pabs T (pctx_cat C₀ C)
    | papp₁ C t        => papp₁ (pctx_cat C₀ C) t
    | papp₂ t C        => papp₂ t (pctx_cat C₀ C)
    | pite₁ C t₂ t₃    => pite₁ (pctx_cat C₀ C) t₂ t₃
    | pite₂ t₁ C t₃    => pite₂ t₁ (pctx_cat C₀ C) t₃
    | pite₃ t₁ t₂ C    => pite₃ t₁ t₂ (pctx_cat C₀ C)
    | ppair₁ C t       => ppair₁ (pctx_cat C₀ C) t
    | ppair₂ t C       => ppair₂ t (pctx_cat C₀ C)
    | pproj₁ C         => pproj₁ (pctx_cat C₀ C)
    | pproj₂ C         => pproj₂ (pctx_cat C₀ C)
    | pinl C           => pinl (pctx_cat C₀ C)
    | pinr C           => pinr (pctx_cat C₀ C)
    | pcaseof₁ C t₁ t₂ => pcaseof₁ (pctx_cat C₀ C) t₁ t₂
    | pcaseof₂ t₁ C t₂ => pcaseof₂ t₁ (pctx_cat C₀ C) t₂
    | pcaseof₃ t₁ t₂ C => pcaseof₃ t₁ t₂ (pctx_cat C₀ C)
    | pseq₁ C t        => pseq₁ (pctx_cat C₀ C) t
    | pseq₂ t C        => pseq₂ t (pctx_cat C₀ C)
    | pfixt τ₁ τ₂ C    => pfixt τ₁ τ₂ (pctx_cat C₀ C)
  end.


(** ** Typing environments. *)

Inductive Env : Set :=
  | empty
  | evar (Γ : Env) (τ : Ty).

Fixpoint dom (Γ: Env) : Dom :=
  match Γ with
    | empty    => O
    | evar Γ τ => S (dom Γ)
  end.
Notation "Γ ▻ T" := (evar Γ T) (at level 55, left associativity).

Reserved Notation "Γ₁ ▻▻ Γ₂" (at level 55, left associativity).
Fixpoint ecat (Γ₁ Γ₂ : Env) {struct Γ₂} : Env :=
  match Γ₂ with
    | empty  => Γ₁
    | Γ₂ ▻ τ => (Γ₁ ▻▻ Γ₂) ▻ τ
  end
where "Γ₁ ▻▻ Γ₂" := (ecat Γ₁ Γ₂).

(** * Morphisms *)

(** ** Common *)

(** Extension of morphisms. *)
Definition snoc {A: Type} (xs: Ix → A) (x: A) : Ix → A :=
  fun i =>
    match i with
      | O   => x
      | S i => xs i
    end.
Notation "xs · x" := (snoc xs x) (at level 55, left associativity).
Arguments snoc {_} xs x i.

(** Moving morphisms under binders *)
Class UpArr (mor: Type) := up : mor → mor.

(** Never unfold automatically. We encode the desired reduction
    behaviour using rewrite rules. *)
Arguments up {_ _} ζ : simpl never.
Notation "m ↑" :=
  (up m) (at level 53, left associativity).

Fixpoint ups {mor: Type} `{UpArr mor} (υ: mor) (δ: Dom) : mor :=
  match δ with
    | O   => υ
    | S δ => ups υ δ ↑
  end.
Arguments ups {_ _} υ !δ /.
Notation "m ↑⋆ δ" :=
  (ups m δ) (at level 53, left associativity).

Class Apply (mor tm: Type) := ap : mor → tm → tm.
Arguments ap {_ _ _} ζ !t /.
Notation "t '[' m ']'" :=
  (ap m t) (at level 8, left associativity, format "t [ m ]").


(** ** Renamings *)

Definition Ren : Set := Ix → Ix.
Definition WsRen (γ₁ γ₂: Dom) (ξ: Ren) : Prop :=
  ∀ i, γ₁ ∋ i → γ₂ ∋ ξ i.

Definition ren_comp (ξ₁ ξ₂ : Ren) : Ren := fun i => ξ₂ (ξ₁ i).
Notation "ξ₁ >-> ξ₂" := (ren_comp ξ₁ ξ₂) (at level 56).
Definition ren_id : Ren := fun i => i.
Instance ren_up : UpArr Ren := fun ξ => (ξ >-> wkl 1) · 0.

Instance applyRenTm : Apply Ren Tm :=
  fix renTm (ξ: Ren) (t : Tm) : Tm :=
  match t with
    | var x           => var (ξ x)
    | abs T t₂        => abs T (renTm (ξ↑) t₂)
    | app t₁ t₂       => app (renTm ξ t₁) (renTm ξ t₂)
    | unit            => unit
    | true            => true
    | false           => false
    | ite t₁ t₂ t₃    => ite (renTm ξ t₁) (renTm ξ t₂) (renTm ξ t₃)
    | pair t₁ t₂      => pair (renTm ξ t₁) (renTm ξ t₂)
    | proj₁ t         => proj₁ (renTm ξ t)
    | proj₂ t         => proj₂ (renTm ξ t)
    | inl t           => inl (renTm ξ t)
    | inr t           => inr (renTm ξ t)
    | caseof t₁ t₂ t₃ => caseof (renTm ξ t₁) (renTm (ξ↑) t₂) (renTm (ξ↑) t₃)
    | seq t₁ t₂       => seq (renTm ξ t₁) (renTm ξ t₂)
    | fixt τ₁ τ₂ t    => fixt τ₁ τ₂ (renTm ξ t)
  end.

Fixpoint ren_beta (δ: Dom) (ξ: Ren) : Ren :=
  fun i =>
    match δ with
      | O   => i
      | S δ => match i with
                 | O   => ξ O
                 | S i => ren_beta δ (wkl 1 >-> ξ) i
               end
    end.


(** ** Substitutions *)

Definition Sub : Set := Ix → Tm.
Definition WsSub (γ₁ γ₂: Dom) (ζ: Sub) : Prop :=
  ∀ i, γ₁ ∋ i → wsTm γ₂ (ζ i).

Definition sub_id : Sub := fun i => var i.
Definition sub_comp_ren (ζ: Sub) (ξ: Ren) : Sub :=
  fun i => (ζ i)[ξ].
Instance sub_up : UpArr Sub :=
  fun ζ => sub_comp_ren ζ (wkl 1) · var 0.

Instance applySubTm : Apply Sub Tm :=
  fix subTm (ζ: Sub) (t : Tm) : Tm :=
  match t with
    | var x           => ζ x
    | abs T t₂        => abs T (subTm (ζ↑) t₂)
    | app t₁ t₂       => app (subTm ζ t₁) (subTm ζ t₂)
    | unit            => unit
    | true            => true
    | false           => false
    | ite t₁ t₂ t₃    => ite (subTm ζ t₁) (subTm ζ t₂) (subTm ζ t₃)
    | pair t₁ t₂      => pair (subTm ζ t₁) (subTm ζ t₂)
    | proj₁ t         => proj₁ (subTm ζ t)
    | proj₂ t         => proj₂ (subTm ζ t)
    | inl t           => inl (subTm ζ t)
    | inr t           => inr (subTm ζ t)
    | caseof t₁ t₂ t₃ => caseof (subTm ζ t₁) (subTm (ζ↑) t₂) (subTm (ζ↑) t₃)
    | seq t₁ t₂       => seq (subTm ζ t₁) (subTm ζ t₂)
    | fixt τ₁ τ₂ t    => fixt τ₁ τ₂ (subTm ζ t)
  end.

Definition sub_comp (ζ₁ ζ₂ : Sub) : Sub := fun i => (ζ₁ i)[ζ₂].
Notation "ζ₁ >=> ζ₂" := (sub_comp ζ₁ ζ₂) (at level 56).
Arguments sub_comp ζ₁ ζ₂ i /.

Definition ren_toSub (ξ: Ren) : Sub := fun i => var (ξ i).
Notation "⌈ ρ ⌉" := (ren_toSub ρ) (format "⌈ ρ ⌉").

Fixpoint sub_beta (δ: Dom) (ζ: Sub) : Sub :=
  fun i =>
    match δ with
      | O   => var i
      | S δ => match i with
                 | O   => ζ O
                 | S i => sub_beta δ (⌈wkl 1⌉ >=> ζ) i
               end
    end.
Arguments sub_beta !δ ζ !i /.

Definition sub_beta1 (t: Tm) : Sub := sub_beta 1 (sub_id · t).
Definition subst0 (t' t: Tm) : Tm := t[sub_beta1 t'].

(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)
