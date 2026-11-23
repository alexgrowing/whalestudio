import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionCommPositiveUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWeilAction_comm_positiveUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) ∧ (∀ γ ∈ UU E N, weil Ψ γ (fun x => φ (h * x)) = fun x => weil Ψ γ φ (h * x)) ∧ ∀ Z ∈ Hn Ψ N, thH Ψ (fun x => φ (h * x)) Z 0 0 = thH Ψ φ Z 0 0 ∧ eis Ψ (fun x => φ (h * x)) Z 0 0 = eis Ψ φ Z 0 0 := by
  first | exact @GlobalTheory.SW.weil_comp_unitary | exact GlobalTheory.SW.weil_comp_unitary | (intros; apply GlobalTheory.SW.weil_comp_unitary <;> assumption)
