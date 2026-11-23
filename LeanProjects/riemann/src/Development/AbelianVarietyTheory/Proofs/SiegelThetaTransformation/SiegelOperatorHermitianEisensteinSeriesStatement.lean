import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelOperatorHermitianEisensteinSeries
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelOperator_hermitianEisensteinSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → ∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => eis Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 (eis Ψ (dropF φ) (dropZ Ψ Z) 0 0)) := by
  first | exact @GlobalTheory.SW.eis_siegel_operator | exact GlobalTheory.SW.eis_siegel_operator | (intros; apply GlobalTheory.SW.eis_siegel_operator <;> assumption)
