import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonempty
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiprojective_points_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, ι k) → Ω), (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → (mcPts (mCoordIdeal x)).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty <;> assumption)
