import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionMetricCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_composition_metric_compat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → h.IsCInf → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y + Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y = Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y + Met.bcDens (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  first | exact @GlobalTheory.CurveDens.bcDens_add_bcDens_stage | exact GlobalTheory.CurveDens.bcDens_add_bcDens_stage | (intros; apply GlobalTheory.CurveDens.bcDens_add_bcDens_stage <;> assumption)
