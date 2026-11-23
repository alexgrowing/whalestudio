import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleLatticeFamilyHermitianWeilAction
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ c R : ℕ, 0 < c → ∃ R' : ℕ, ∀ (M : ℕ) (φ : Fam E n N), admitted M R φ → ∀ γ ∈ UU E N, Den c γ → admitted M R' (fun Λ => weil Ψ γ (φ Λ)) := by
  first | exact @GlobalTheory.SW.weil_admissible | exact GlobalTheory.SW.weil_admissible | (intros; apply GlobalTheory.SW.weil_admissible <;> assumption)
