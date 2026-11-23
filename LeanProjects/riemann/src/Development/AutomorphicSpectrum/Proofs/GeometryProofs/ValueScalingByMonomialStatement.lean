import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueScalingByMonomial
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemPtsOverOfMemMcPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneMemChartLatNm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_scaling_by_monomial : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L) (a : K → ℤ) (s : Ω) (w : L), Small.HasVal y (0 : K → ℤ) s z w → w ≠ 0 → ∀ c : (k : K) → J k, (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k, z ⟨k, c k⟩ ≠ 0) → ∃ v : L, v ≠ 0 ∧ Small.HasVal y a (s * ∏ k, y ⟨k, c k⟩ ^ a k) z v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartTwist.hasVal_twist | exact GlobalTheory.CompanionTheory.Ar.ChartTwist.hasVal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartTwist.hasVal_twist <;> assumption)
