import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFinite
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ, DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | exact GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | (intros; apply GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite <;> assumption)
