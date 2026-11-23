import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorOfIntegralMatrix
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_minor_of_integral_matrix : ∀ (p : ℕ) [Fact p.Prime] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J] (c : Matrix κ J ℂ_[p]),
  (∀ k i, ‖c k i‖ ≤ 1) →
  (∀ a : κ → ℂ_[p], (∀ i, ‖∑ k, a k * c k i‖ ≤ 1) → ∀ k, ‖a k‖ ≤ 1) →
  ∃ f : κ → J, Function.Injective f ∧ ‖(c.submatrix id f).det‖ = 1 := by
  first | exact @GlobalTheory.SatMinor.exists_minor_norm_one | exact GlobalTheory.SatMinor.exists_minor_norm_one | (intros; apply GlobalTheory.SatMinor.exists_minor_norm_one <;> assumption)
