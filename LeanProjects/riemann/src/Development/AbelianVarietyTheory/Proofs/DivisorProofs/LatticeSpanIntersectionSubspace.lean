import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreMore
open NumberField

namespace GlobalTheory

theorem exists_ringOfIntegers_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {r : ℕ}
    (E : Submodule (𝓞 K) (Fin r → K)) {v : Fin r → K}
    (hv : v ∈ Submodule.span K (E : Set (Fin r → K))) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ E := by
  first
  | exact @_root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ScalarMultipleInSpan.exists_smul_mem_of_mem_span ..)

theorem span_inf_eq_of_span_eq_top (K : Type) [Field K] [NumberField K] (r : ℕ)
    (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K))
    (hE : Submodule.span K (E : Set (Fin r → K)) = ⊤) :
    Submodule.span K ((E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) :
      Set (Fin r → K)) = V := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    have hv' : v ∈ Submodule.span K (E : Set (Fin r → K)) := by rw [hE]; trivial
    obtain ⟨d, hd, hdv⟩ := exists_ringOfIntegers_smul_mem_of_mem_span E hv'
    have hdK : (algebraMap (𝓞 K) K d) ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    have hmem : d • v ∈ (E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) := by
      refine Submodule.mem_inf.mpr ⟨hdv, ?_⟩
      show d • v ∈ V
      rw [← algebraMap_smul K d]
      exact V.smul_mem _ hv
    have key : v = (algebraMap (𝓞 K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_cut : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K)), Submodule.span K (E : Set (Fin r → K)) = ⊤ → Submodule.span K ((E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) : Set (Fin r → K)) = V :=
  fun K _ _ r E V hE => span_inf_eq_of_span_eq_top K r E V hE

end GlobalTheory
