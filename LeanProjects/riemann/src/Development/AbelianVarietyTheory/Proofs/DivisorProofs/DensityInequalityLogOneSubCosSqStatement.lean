import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityInequalityLogOneSubCosSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_inequality_log_one_sub_cosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (κ κ' δ : AlgChart p σ 1 → CxPts p σ → ℝ), IsDens κ → IsDens κ' → IsDens δ → ∀ (v f : CxPts p σ → ℝ) (S : Set (CxPts p σ)), Continuous v → (∀ y, 0 ≤ v y ∧ v y ≤ 1) → IsOpen S → Sᶜ.Finite → (∀ y ∈ S, v y < 1 ∧ f y = Real.log (1 - v y) / 2) → IntegrableOn f S (part κ) → IntegrableOn f S (part fun c y => -κ c y) → IntegrableOn f S (part κ') → IntegrableOn f S (part fun c y => -κ' c y) → (∀ n : ℕ, total (fun c y => v y ^ (n + 1) * (κ c y - κ' c y) + (n + 1) * v y ^ n * (1 - v y) * δ c y) = 0) → 2 * ((∫ y in S, f y ∂(part κ) - ∫ y in S, f y ∂(part fun c y => -κ c y)) - (∫ y in S, f y ∂(part κ') - ∫ y in S, f y ∂(part fun c y => -κ' c y))) = total δ := by
  first | exact @GlobalTheory.CurveDens.green_sum | exact GlobalTheory.CurveDens.green_sum | (intros; apply GlobalTheory.CurveDens.green_sum <;> assumption)
