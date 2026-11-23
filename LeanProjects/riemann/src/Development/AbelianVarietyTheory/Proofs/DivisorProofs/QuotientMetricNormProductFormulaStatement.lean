import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMetricNormProductFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_metric_norm_product_formula : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1) (h₃ : IsVB S.X₃ 1) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)), IsFrame (fun _ : Fin 1 => t) → ∀ y ∈ ptsIn p σ U, ((h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y).re * (h.form (S.f.app U t) (S.f.app U t) y).re = (h.form w w y).re * (h.form (S.f.app U t) (S.f.app U t) y).re - ‖h.form w (S.f.app U t) y‖ ^ 2 := by
  first | exact @GlobalTheory.CurveDens.quot_form_pyth_rankTwo | exact GlobalTheory.CurveDens.quot_form_pyth_rankTwo | (intros; apply GlobalTheory.CurveDens.quot_form_pyth_rankTwo <;> assumption)
