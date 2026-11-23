import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTheta_summable_and_determines_testFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → ∀ Z ∈ Hn Ψ N, (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * expo Ψ x Z z z')‖) ∧ ∀ ψ, IsSB ψ → (∀ z z', thH Ψ φ Z z z' = thH Ψ ψ Z z z') → φ = ψ := by
  first | exact @GlobalTheory.SW.thH_summable_and_inj | exact GlobalTheory.SW.thH_summable_and_inj | (intros; apply GlobalTheory.SW.thH_summable_and_inj <;> assumption)
