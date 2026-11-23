import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_base_projection_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j), (∀ z ∈ mcPts (mCoordIdeal y), basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) ∧ (∀ zb ∈ mcPts (mCoordIdeal M.x), ∃ F, M.IsFrame F ∧ M.GoodAt F (mCoordIdeal zb)) ∧ ∀ F, M.IsFrame F → ∀ z : (Σ k, ι k) → ℂ, basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) → (z ∈ mcPts (mCoordIdeal y) ↔ ∃ h, M.IsFlagOf F z h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CPts.main | exact GlobalTheory.CompanionTheory.Ar.PB.CPts.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CPts.main <;> assumption)
