import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesOfSchwartzIsHolomorphic
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_of_schwartz_is_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsHeat Ψ (eis Ψ φ) := by
  first | exact @GlobalTheory.SW.isHeat_eis | exact GlobalTheory.SW.isHeat_eis | (intros; apply GlobalTheory.SW.isHeat_eis <;> assumption)
