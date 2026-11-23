import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialSubring_maximal_integral : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧ ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  first | exact @GlobalTheory.exists_polySubring_maximal_integral | exact GlobalTheory.exists_polySubring_maximal_integral | (intros; apply GlobalTheory.exists_polySubring_maximal_integral <;> assumption)
