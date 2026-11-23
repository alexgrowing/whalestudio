import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceInvariantNormBounded
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ M R : ℕ, ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ, (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ Hn Ψ (N + 1), ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  first | exact @GlobalTheory.SW.swd_invariant_bound | exact GlobalTheory.SW.swd_invariant_bound | (intros; apply GlobalTheory.SW.swd_invariant_bound <;> assumption)
