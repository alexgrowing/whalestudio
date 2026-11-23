import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  first | exact @GlobalTheory.LocInj.locInj | exact GlobalTheory.LocInj.locInj | (intros; apply GlobalTheory.LocInj.locInj <;> assumption)
