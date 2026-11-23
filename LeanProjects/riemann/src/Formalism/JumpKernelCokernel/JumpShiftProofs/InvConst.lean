import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths

theorem fil_eq_of_noJump {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (Fil : ℤ → Submodule K D) (b η : ℕ)
    (hj : ∀ j : ℤ, -(b : ℤ) < j → j < -(η : ℤ) → Fil j = Fil (j + 1)) :
    ∀ k : ℕ, ∀ j : ℤ, -(b : ℤ) < j → j + k = -(η : ℤ) → Fil j = Fil (-(η : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro j _ hjk
    simp only [Nat.cast_zero, add_zero] at hjk
    rw [hjk]
  | succ k ih =>
    intro j hjb hjk
    have hlt : j < -(η : ℤ) := by push_cast at hjk; omega
    rw [hj j hjb hlt]
    exact ih (j + 1) (by omega) (by push_cast at hjk ⊢; omega)

theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro K _ D _ _ Fil hA χ hχ b η w hj hw
  have h1 : ∀ i : ℤ, i ≠ 0 → w i ∈ Fil (-i) := by
    intro i hi
    have hne : χ ^ i - 1 ≠ 0 := sub_ne_zero.mpr (hχ i hi)
    have h2 := (Fil (-i)).smul_mem (χ ^ i - 1)⁻¹ (hw i)
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  refine ⟨h1, fun i hi hib => ?_⟩
  by_cases hη : (η : ℤ) ≤ i
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, -i + k = -(η : ℤ) := ⟨(i - η).toNat, by omega⟩
    rw [← fil_eq_of_noJump Fil b η hj k (-i) (by omega) hk]
    exact h1 i hi
  · exact hA (by omega : -(η : ℤ) ≤ -i) (h1 i hi)

end Formalism.KernelCokernelLengths
