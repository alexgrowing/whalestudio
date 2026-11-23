import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_gauss_norm_eventually_monomial : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  first | exact @GlobalTheory.MemLoc.gauss_slope | exact GlobalTheory.MemLoc.gauss_slope | (intros; apply GlobalTheory.MemLoc.gauss_slope <;> assumption)
