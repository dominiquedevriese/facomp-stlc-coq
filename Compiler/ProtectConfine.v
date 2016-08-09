Require Stlc.SpecSyntax.
Require Import Utlc.SpecSyntax.

Module SS := Stlc.SpecSyntax.

Fixpoint protect (ty : SS.Ty) : UTm :=
  abs (match ty with
         | SS.tunit => var 0
         | SS.tbool => var 0
         | SS.tarr ty1 ty2 => abs (app (protect ty2) (app (var 1) (app (confine ty1) (var 0))))
         | SS.tprod ty1 ty2 => pair (app (protect ty1) (proj₁ (var 0))) (app (protect ty2) (proj₂ (var 0)))
         | SS.tsum ty1 ty2 => caseof (var 0) (inl (app (protect ty1) (var 0))) (inr (app (protect ty2) (var 0)))
       end)
with confine (ty : SS.Ty) : UTm :=
  abs (match ty with
         | SS.tunit => seq (var 0) unit
         | SS.tbool => ite (var 0) true false
         | SS.tarr ty1 ty2 => abs (app (confine ty2) (app (var 1) (app (protect ty1) (var 0))))
         | SS.tprod ty1 ty2 => pair (app (confine ty1) (proj₁ (var 0))) (app (confine ty2) (proj₂ (var 0)))
         | SS.tsum ty1 ty2 => caseof (var 0) (inl (app (confine ty1) (var 0))) (inr (app (confine ty2) (var 0)))
       end).

