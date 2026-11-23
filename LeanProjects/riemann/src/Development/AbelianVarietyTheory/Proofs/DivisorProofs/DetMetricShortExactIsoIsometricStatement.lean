import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_metric_shortExact_iso_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (S S' : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (h' : VMetric p S'.X₂ (r + s)) (H : h.IsCInf) (H' : h'.IsCInf) (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂), e₁.hom ≫ S'.f = S.f ≫ e₂.hom → h.IsIsometry h' e₂ → (VMetric.det (H.quot hS h₁ h₃)).Isometric (VMetric.det (H'.quot hS' h₁' h₃')) ∧ h.bcInt hS h₁ h₃ = h'.bcInt hS' h₁' h₃' := by
  first | exact @GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso | exact GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso | (intros; apply GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso <;> assumption)
