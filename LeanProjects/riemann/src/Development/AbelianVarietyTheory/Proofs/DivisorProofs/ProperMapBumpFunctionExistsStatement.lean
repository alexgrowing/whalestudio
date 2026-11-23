import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperMapBumpFunctionExists
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_map_bump_function_exists : ∀ {P U : Type} [TopologicalSpace P] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (π : P → U), Continuous π → ∀ (W' : Set U), IsOpen W' →
    (∀ S : Set U, IsCompact S → S ⊆ W' → IsCompact (π ⁻¹' S)) → ∀ (p₀ : P), π p₀ ∈ W' →
    ∀ (O : Set P), IsOpen O → π ⁻¹' {π p₀} ⊆ O →
    ∃ (φ : SchwartzMap U ℂ) (C : Set P), (∀ x, (φ x).im = 0 ∧ 0 ≤ (φ x).re) ∧ 0 < (φ (π p₀)).re ∧ IsCompact C ∧ C ⊆ O ∧
      ∀ p ∉ C, φ (π p) = 0 := by
  first | exact @GlobalTheory.exists_schwartz_bump_of_proper_onto_open | exact GlobalTheory.exists_schwartz_bump_of_proper_onto_open | (intros; apply GlobalTheory.exists_schwartz_bump_of_proper_onto_open <;> assumption)
