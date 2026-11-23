import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumberFieldLatticeClearsDenominator
import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_lattice_clears_denominator : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)), Submodule.span K (L : Set (Fin m → K)) = ⊤ → ∀ x : Fin m → K, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ L := by
  first | exact @GlobalTheory.exists_ne_zero_smul_mem_of_kspan_eq_top | exact GlobalTheory.exists_ne_zero_smul_mem_of_kspan_eq_top | (intros; apply GlobalTheory.exists_ne_zero_smul_mem_of_kspan_eq_top <;> assumption)
