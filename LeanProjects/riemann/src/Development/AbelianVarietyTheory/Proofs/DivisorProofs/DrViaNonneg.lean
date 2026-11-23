import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Toroidal Formalism.L2.Geo

namespace GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

def drVia (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (y : Sp K ⟶ (Φ.C k).Y.X)
    (φ : K →+* ℂ_[p]) (f : (Φ.C k).Y.Fn) : ℝ :=
  ‖φ (GlobalTheory.TrueGeo.valAt y (f * ((∏ z : Letter S.Dw, (((Φ.C k).gr_spec (below y)).choose_spec.choose_spec.choose z.1 z.2) ^
      expo S.Dw (drSym la) z : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn)))‖ *
    Real.exp ((drSym la).sum fun a n => (n : ℝ) * lnStep s.T.Z.t
      (spMap (φ.comp (Scheme.stalkClosedPointTo y).hom) ≫ stalkPt (Φ.C k).Y (below y) ≫ (Φ.C k).π ≫ genι s.T.Z)
      (fun τ i => spMap (dualMap (φ.comp (Scheme.stalkClosedPointTo y).hom)) ≫
        ((Φ.C k).gr_spec (below y)).choose_spec.choose.v τ i) p (a.1 p) a.2.2)

theorem drVia_nonneg (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (y : Sp K ⟶ (Φ.C k).Y.X)
    (φ : K →+* ℂ_[p]) (f : (Φ.C k).Y.Fn) : 0 ≤ drVia Φ k la p y φ f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

end GlobalTheory.CovHt.Link
