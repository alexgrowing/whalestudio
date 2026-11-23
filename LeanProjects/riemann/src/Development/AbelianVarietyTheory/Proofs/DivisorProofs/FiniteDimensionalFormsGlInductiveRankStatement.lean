import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlInductiveRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_forms_gl_inductive_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ)) (ψ : Sm E n), IsAutForm ψ → (∀ k ∈ L', finRep E n k ψ = ψ) → (∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') → ∀ ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E n) => z ψ) '' Zalg E n), IsAutForm ψ' ∧ (∀ k ∈ L', finRep E n k ψ' = ψ') ∧ ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ').1 g) ∈ W' := by
  first | exact @GlobalTheory.CentreInherit.centre_preserves_forms | exact GlobalTheory.CentreInherit.centre_preserves_forms | (intros; apply GlobalTheory.CentreInherit.centre_preserves_forms <;> assumption)
