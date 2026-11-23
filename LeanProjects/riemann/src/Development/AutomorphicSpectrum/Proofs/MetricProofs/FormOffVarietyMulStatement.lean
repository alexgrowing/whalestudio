import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormOffVarietyMul
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_off_variety_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (u v : MRing ι), IsArithVar (mCoordIdeal y) d → IsFormOff (mCoordIdeal y) u → IsFormOff (mCoordIdeal y) v → IsFormOff (mCoordIdeal y) (u * v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.isFormOff_mul_of_arith | exact GlobalTheory.CompanionTheory.Ar.Small.isFormOff_mul_of_arith | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.isFormOff_mul_of_arith <;> assumption)
