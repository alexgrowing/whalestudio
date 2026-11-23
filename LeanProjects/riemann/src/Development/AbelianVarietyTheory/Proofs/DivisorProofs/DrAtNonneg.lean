import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Toroidal Formalism.L2.Geo

namespace GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

def drAt (la : AllWt.Weight S.Dw) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ)
    (x : Sp C ⟶ (Φ.C k).Y.X) (f : (Φ.C k).Y.Fn) : ℝ :=
  ‖GlobalTheory.TrueGeo.valAt x (f * ((∏ z : Letter S.Dw, (((Φ.C k).gr_spec (below x)).choose_spec.choose_spec.choose z.1 z.2) ^
               expo S.Dw (drSym la) z : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))‖ *
    Real.exp ((drSym la).sum fun a n => (n : ℝ) * lnStep s.T.Z.t
      (spMap (Scheme.stalkClosedPointTo x).hom ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z)
      (fun τ i => spMap (dualMap (Scheme.stalkClosedPointTo x).hom) ≫
        ((Φ.C k).gr_spec (below x)).choose_spec.choose.v τ i) p (a.1 p) a.2.2)

theorem drAt_nonneg (la : AllWt.Weight S.Dw) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ)
    (x : Sp C ⟶ (Φ.C k).Y.X) (f : (Φ.C k).Y.Fn) : 0 ≤ drAt Φ k la p x f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

end GlobalTheory.CovHt.Link
