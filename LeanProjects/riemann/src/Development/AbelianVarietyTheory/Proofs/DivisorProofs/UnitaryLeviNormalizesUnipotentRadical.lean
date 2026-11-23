import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem levi_mul_rad_apply {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n}
    (hm : ∀ i j, β i ≠ β j → mat m i j = 0)
    (hu : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j) {i l : Fin n} (h : β l ≤ β i) :
    mat (m * u) i l = mat m i l := by
  rw [mat_mul, Matrix.mul_apply]
  have key : ∀ k, mat m i k * mat u k l = mat m i k * (1 : Matrix (Fin n) (Fin n) L) k l := by
    intro k
    by_cases hk : β i = β k
    · rw [hu k l (by rw [← hk]; exact h)]
    · rw [hm i k hk, zero_mul, zero_mul]
  simp_rw [key]
  rw [← Matrix.mul_apply, Matrix.mul_one]

theorem leviRad : LeviRad := by
  intro L _ _ σ n β hσ m hm u hu
  refine ⟨?_, fun hmu => ?_⟩
  · show ∀ i j, β j ≤ β i → mat (m * u * m⁻¹) i j = (1 : Matrix (Fin n) (Fin n) L) i j
    intro i l h
    have hmi : m⁻¹ ∈ leviU σ β := inv_mem hm
    rw [mat_mul, Matrix.mul_apply]
    have key : ∀ k, mat (m * u) i k * mat m⁻¹ k l = mat m i k * mat m⁻¹ k l := by
      intro k
      by_cases hk : β k = β l
      · rw [levi_mul_rad_apply hm hu (by rw [hk]; exact h)]
      · rw [hmi k l hk, mul_zero, mul_zero]
    simp_rw [key]
    rw [← Matrix.mul_apply, ← mat_mul, mul_inv_cancel, mat_one]
  · rw [mem_KU_iff hσ] at hmu ⊢
    intro i l
    by_cases hk : β i = β l
    · rw [← levi_mul_rad_apply hm hu (le_of_eq hk.symm)]
      exact hmu i l
    · rw [hm i l hk]
      exact zero_mem _

end GlobalTheory.SatakeWeyl
