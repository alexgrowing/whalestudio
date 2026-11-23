import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarQuotientFormBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_dbar_quotient_form_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1) (h₃ : IsVB S.X₃ 1), h.IsCInf → ∀ (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)), IsFrame (fun _ : Fin 1 => t) → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ‖dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1) - h.form w (S.f.app U t) y * dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ)) (c.e y) (EuclideanSpace.single 0 1)‖ ^ 2 = ((h.form (S.f.app U t) (S.f.app U t) y).re * (h.form w w y).re - ‖h.form w (S.f.app U t) y‖ ^ 2) * (Real.pi * h.bcDens hS h₁ h₃ c y) := by
  first | exact @GlobalTheory.CurveDens.norm_dbar_projection_sq | exact GlobalTheory.CurveDens.norm_dbar_projection_sq | (intros; apply GlobalTheory.CurveDens.norm_dbar_projection_sq <;> assumption)
