import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianRestrictionOrthonormalCoords
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_restriction_orthonormal_coords : ∀ (g m : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ W : Submodule ℂ (Fin g → ℂ), Module.finrank ℂ W = m → ∃ c : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W, z' ⬝ᵥ Hm *ᵥ star z = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | exact GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords <;> assumption)
