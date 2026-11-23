import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsUniformlySmallOutsideCompactBand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_uniformly_small_outside_compact_band : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧ ∀ g ∈ band E a, (∃ γ : GL (Fin a) E, ratGL E a γ * g ∈ C) ∨ ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ‖φ.1 g‖ ≤ ε * M := by
  first | exact @GlobalTheory.HCF.Tail.tails | exact GlobalTheory.HCF.Tail.tails | (intros; apply GlobalTheory.HCF.Tail.tails <;> assumption)
