import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperator
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ), IsSB φ → IsSB (dropF φ) ∧ ∀ Z ∈ Hn Ψ (N + 1), dropZ Ψ Z ∈ Hn Ψ N ∧ (∀ t : ℝ, 0 ≤ t → pushZ Ψ Z (Pi.single 0 1) t ∈ Hn Ψ (N + 1)) ∧ ∀ z z' : CM Ψ n (N + 1), Tendsto (fun t : ℝ => thH Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) z z') atTop (𝓝 (thH Ψ (dropF φ) (dropZ Ψ Z) (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))) := by
  first | exact @GlobalTheory.SW.thH_siegel_operator | exact GlobalTheory.SW.thH_siegel_operator | (intros; apply GlobalTheory.SW.thH_siegel_operator <;> assumption)
