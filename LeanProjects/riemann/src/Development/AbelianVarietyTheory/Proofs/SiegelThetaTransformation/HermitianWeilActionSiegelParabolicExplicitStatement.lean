import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicit
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → (∀ γ ∈ UU E N, γ.toBlocks₂₁ = 0 → ∀ x, weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) * chiH Ψ (-(γ.toBlocks₁₂ * ccT γ.toBlocks₁₁)) x * φ (x * γ.toBlocks₁₁)) ∧ ∀ γ ∈ UU E N, ∀ γ' ∈ UU E N, botSpan γ = botSpan γ' → ∀ Z ∈ Hn Ψ N, ∀ z z', eisTerm Ψ γ φ Z z z' = eisTerm Ψ γ' φ Z z z' := by
  first | exact @GlobalTheory.SW.weil_parabolic | exact GlobalTheory.SW.weil_parabolic | (intros; apply GlobalTheory.SW.weil_parabolic <;> assumption)
