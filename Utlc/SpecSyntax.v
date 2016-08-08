Require Export Db.Spec.

Inductive UTm : Set :=
  | wrong
  | var (i: Ix)
  | abs (t: UTm)
  | app (t₁ t₂: UTm)
  | unit
  | true
  | false
  | ite (t₁ t₂ t₃: UTm)
  | pair (t₁ t₂: UTm)
  | proj₁ (t: UTm)
  | proj₂ (t: UTm)
  | inl (t: UTm)
  | inr (t: UTm)
  | caseof (t₁ t₂ t₃: UTm)
  | seq (t₁ t₂: UTm).

(** ** Program contexts *)

Inductive PCtx : Set :=
  | phole
  | pabs (C: PCtx)
  | papp₁ (C: PCtx) (t: UTm)
  | papp₂ (t: UTm) (C: PCtx)
  | pite₁ (C: PCtx) (t₂ t₃: UTm)
  | pite₂ (t₁: UTm) (C: PCtx) (t₃: UTm)
  | pite₃ (t₁ t₂: UTm) (C: PCtx)
  | ppair₁ (C: PCtx) (t: UTm)
  | ppair₂ (t: UTm) (C: PCtx)
  | pproj₁ (C: PCtx)
  | pproj₂ (C: PCtx)
  | pinl (C: PCtx)
  | pinr (C: PCtx)
  | pcaseof₁ (C: PCtx) (t₂ t₃: UTm)
  | pcaseof₂ (t₁: UTm) (C: PCtx) (t₃: UTm)
  | pcaseof₃ (t₁ t₂: UTm) (C: PCtx)
  | pseq₁ (C: PCtx) (t: UTm)
  | pseq₂ (t: UTm) (C: PCtx).

Fixpoint pctx_app (t₀: UTm) (C: PCtx) {struct C} : UTm :=
  match C with
    | phole            => t₀
    | pabs C           => abs (pctx_app t₀ C)
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
  end.

Fixpoint pctx_cat (C₀ C: PCtx) {struct C} : PCtx :=
  match C with
    | phole            => C₀
    | pabs C           => pabs (pctx_cat C₀ C)
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
  end.

(** ** Substitution *)

Section Application.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {wkY: Wk Y}.
  Context {vrUTm: Vr UTm}.
  Context {liftYUTm: Lift Y UTm}.

  Fixpoint apUTm (ζ: Sub Y) (t: UTm) {struct t} : UTm :=
    match t with
      | wrong           => wrong
      | var x           => lift (ζ x)
      | abs t           => abs (apUTm (ζ↑) t)
      | app t₁ t₂       => app (apUTm ζ t₁) (apUTm ζ t₂)
      | unit            => unit
      | true            => true
      | false           => false
      | ite t₁ t₂ t₃    => ite (apUTm ζ t₁) (apUTm ζ t₂) (apUTm ζ t₃)
      | pair t₁ t₂      => pair (apUTm ζ t₁) (apUTm ζ t₂)
      | proj₁ t         => proj₁ (apUTm ζ t)
      | proj₂ t         => proj₂ (apUTm ζ t)
      | inl t           => inl (apUTm ζ t)
      | inr t           => inr (apUTm ζ t)
      | caseof t₁ t₂ t₃ => caseof (apUTm ζ t₁) (apUTm (ζ↑) t₂) (apUTm (ζ↑) t₃)
      | seq t₁ t₂       => seq (apUTm ζ t₁) (apUTm ζ t₂)
    end.

  Fixpoint apPCtx (ζ: Sub Y) (C: PCtx) {struct C} : PCtx :=
    match C with
      | phole            => phole
      | pabs C           => pabs (apPCtx ζ↑ C)
      | papp₁ C t        => papp₁ (apPCtx ζ C) (apUTm ζ t)
      | papp₂ t C        => papp₂ (apUTm ζ t) (apPCtx ζ C)
      | pite₁ C t₂ t₃    => pite₁ (apPCtx ζ C) (apUTm ζ t₂) (apUTm ζ t₃)
      | pite₂ t₁ C t₃    => pite₂ (apUTm ζ t₁) (apPCtx ζ C) (apUTm ζ t₃)
      | pite₃ t₁ t₂ C    => pite₃ (apUTm ζ t₁) (apUTm ζ t₂) (apPCtx ζ C)
      | ppair₁ C t       => ppair₁ (apPCtx ζ C) (apUTm ζ t)
      | ppair₂ t C       => ppair₂ (apUTm ζ t) (apPCtx ζ C)
      | pproj₁ C         => pproj₁ (apPCtx ζ C)
      | pproj₂ C         => pproj₂ (apPCtx ζ C)
      | pinl C           => pinl (apPCtx ζ C)
      | pinr C           => pinr (apPCtx ζ C)
      | pcaseof₁ C t₂ t₃ => pcaseof₁ (apPCtx ζ C) (apUTm ζ↑ t₂) (apUTm ζ↑ t₃)
      | pcaseof₂ t₁ C t₃ => pcaseof₂ (apUTm ζ t₁) (apPCtx ζ↑ C) (apUTm ζ↑ t₃)
      | pcaseof₃ t₁ t₂ C => pcaseof₃ (apUTm ζ t₁) (apUTm ζ↑ t₂) (apPCtx ζ↑ C)
      | pseq₁ C t        => pseq₁ (apPCtx ζ C) (apUTm ζ t)
      | pseq₂ t C        => pseq₂ (apUTm ζ t) (apPCtx ζ C)
    end.

End Application.

(* This function calculates the difference between the outer scope of the
   program context and the scope at the hole. Also called the "binding depth" of
   the hole. To obtain the correct order bindings are added on the left side
   which makes it necessary to reason with associativity. Also see lemma
   'ws_pctx_depth' in 'LemmasScoping'.
 *)
Fixpoint depthPCtx (C: PCtx) : Dom :=
  match C with
    | phole => 0
    | pabs C => 1 ∪ depthPCtx C
    | papp₁ C t => depthPCtx C
    | papp₂ t C => depthPCtx C
    | pite₁ C t₂ t₃ => depthPCtx C
    | pite₂ t₁ C t₃ => depthPCtx C
    | pite₃ t₁ t₂ C => depthPCtx C
    | ppair₁ C t => depthPCtx C
    | ppair₂ t C => depthPCtx C
    | pproj₁ C => depthPCtx C
    | pproj₂ C => depthPCtx C
    | pinl C => depthPCtx C
    | pinr C => depthPCtx C
    | pcaseof₁ C t₂ t₃ => depthPCtx C
    | pcaseof₂ t₁ C t₃ => 1 ∪ depthPCtx C
    | pcaseof₃ t₁ t₂ C => 1 ∪ depthPCtx C
    | pseq₁ C t => depthPCtx C
    | pseq₂ t C => depthPCtx C
  end.

(* Same as the above but in reverse order. Slightly better for proofs. *)
Fixpoint depthlPCtx (C: PCtx) : Dom :=
  match C with
    | phole => 0
    | pabs C => depthlPCtx C ∪ 1
    | papp₁ C t => depthlPCtx C
    | papp₂ t C => depthlPCtx C
    | pite₁ C t₂ t₃ => depthlPCtx C
    | pite₂ t₁ C t₃ => depthlPCtx C
    | pite₃ t₁ t₂ C => depthlPCtx C
    | ppair₁ C t => depthlPCtx C
    | ppair₂ t C => depthlPCtx C
    | pproj₁ C => depthlPCtx C
    | pproj₂ C => depthlPCtx C
    | pinl C => depthlPCtx C
    | pinr C => depthlPCtx C
    | pcaseof₁ C t₂ t₃ => depthlPCtx C
    | pcaseof₂ t₁ C t₃ => depthlPCtx C ∪ 1
    | pcaseof₃ t₁ t₂ C => depthlPCtx C ∪ 1
    | pseq₁ C t => depthlPCtx C
    | pseq₂ t C => depthlPCtx C
  end.

Ltac crushUtlcSyntaxMatchH :=
  match goal with
    | [ H: False                        |- _ ] => destruct H
    | [ H: _ ∧ _                        |- _ ] => destruct H
    | [ H: S _          = S _           |- _ ] => apply eq_add_S in H
    | [ H: var _        = var _         |- _ ] => inversion H; clear H
    | [ H: abs _        = abs _         |- _ ] => inversion H; clear H
    | [ H: app _ _      = app _ _       |- _ ] => inversion H; clear H
    | [ H: ite _ _ _    = ite _ _ _     |- _ ] => inversion H; clear H
    | [ H: pair _ _     = pair _ _      |- _ ] => inversion H; clear H
    | [ H: proj₁ _      = proj₁ _       |- _ ] => inversion H; clear H
    | [ H: proj₂ _      = proj₂ _       |- _ ] => inversion H; clear H
    | [ H: inl _        = inl _         |- _ ] => inversion H; clear H
    | [ H: inr _        = inr _         |- _ ] => inversion H; clear H
    | [ H: caseof _ _ _ = caseof _ _ _  |- _ ] => inversion H; clear H
    | [ H: seq _ _      = seq _ _       |- _ ] => inversion H; clear H

    | [ |- S _            = S _            ] => f_equal
    | [ |- wrong          = wrong          ] => f_equal
    | [ |- var _          = var _          ] => f_equal
    | [ |- abs _          = abs _          ] => f_equal
    | [ |- app _ _        = app _ _        ] => f_equal
    | [ |- unit           = unit           ] => reflexivity
    | [ |- true           = true           ] => reflexivity
    | [ |- false          = false          ] => reflexivity
    | [ |- ite _ _ _      = ite _ _ _      ] => f_equal
    | [ |- pair _ _       = pair _ _       ] => f_equal
    | [ |- proj₁ _        = proj₁ _        ] => f_equal
    | [ |- proj₂ _        = proj₂ _        ] => f_equal
    | [ |- inl _          = inl _          ] => f_equal
    | [ |- inr _          = inr _          ] => f_equal
    | [ |- caseof _ _ _   = caseof _ _ _   ] => f_equal
    | [ |- seq _ _        = seq _ _        ] => f_equal
    | [ |- pabs _         = pabs _         ] => f_equal
    | [ |- papp₁ _ _      = papp₁ _ _      ] => f_equal
    | [ |- papp₂ _ _      = papp₂ _ _      ] => f_equal
    | [ |- pite₁ _ _ _    = pite₁ _ _ _    ] => f_equal
    | [ |- pite₂ _ _ _    = pite₂ _ _ _    ] => f_equal
    | [ |- pite₃ _ _ _    = pite₃ _ _ _    ] => f_equal
    | [ |- ppair₁ _ _     = ppair₁ _ _     ] => f_equal
    | [ |- ppair₂ _ _     = ppair₂ _ _     ] => f_equal
    | [ |- pproj₁ _       = pproj₁ _       ] => f_equal
    | [ |- pproj₂ _       = pproj₂ _       ] => f_equal
    | [ |- pinl _         = pinl _         ] => f_equal
    | [ |- pinr _         = pinr _         ] => f_equal
    | [ |- pcaseof₁ _ _ _ = pcaseof₁ _ _ _ ] => f_equal
    | [ |- pcaseof₂ _ _ _ = pcaseof₂ _ _ _ ] => f_equal
    | [ |- pcaseof₃ _ _ _ = pcaseof₃ _ _ _ ] => f_equal
    | [ |- pseq₁ _ _      = pseq₁ _ _      ] => f_equal
    | [ |- pseq₂ _ _      = pseq₂ _ _      ] => f_equal
    | [ |- context[apUTm ?ξ ?t] ] =>
      change (apUTm ξ t) with t[ξ]
    | [ |- context[apPCtx ?ξ ?C] ] =>
      change (apPCtx ξ C) with C[ξ]
  end.

Ltac crushUtlc :=
  intros;
  repeat
    (cbn in *;
     crushRewriteH;
     repeat crushDbMatchH;
     repeat crushUtlcSyntaxMatchH;
     try discriminate;
     try subst);
  eauto.
