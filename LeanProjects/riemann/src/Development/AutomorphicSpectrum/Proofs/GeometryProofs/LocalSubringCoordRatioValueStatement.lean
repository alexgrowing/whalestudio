import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringCoordRatioValue
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemPtsOverOfMemMcPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneMemChartLatNm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_subring_coord_ratio_value : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ (A : Subring Ω) (_ : IsLocalRing A), (∀ (k : K) (a b : J k), z ⟨k, b⟩ ≠ 0 → y ⟨k, b⟩ ≠ 0 ∧ y ⟨k, a⟩ / y ⟨k, b⟩ ∈ A) ∧ (∀ n : ℕ, (n : L) ≠ 0 → (n : Ω) ≠ 0 ∧ (n : Ω)⁻¹ ∈ A) ∧ ∀ s ∈ A, s⁻¹ ∈ A → s ≠ 0 → ∃ w : L, w ≠ 0 ∧ Small.HasVal y (0 : K → ℤ) s z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing | exact GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing <;> assumption)
