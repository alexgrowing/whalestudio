import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open GlobalTheory.DegCmp

section

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def sameDegQuot (ev : V →ₗ[K] Ω) : IntermediateField K Ω where
  carrier := {x | ∃ (e : ℕ) (q : Ω), q ∈ (LinearMap.range ev) ^ e ∧ q ≠ 0 ∧ x * q ∈ (LinearMap.range ev) ^ e}
  mul_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show x * y * (q * q') = (x * q) * (y * q') by ring]
      exact Submodule.mul_mem_mul hxq hyq'
  add_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show (x + y) * (q * q') = (x * q) * q' + q * (y * q') by ring]
      exact Submodule.add_mem _ (Submodule.mul_mem_mul hxq hq') (Submodule.mul_mem_mul hq hyq')
  algebraMap_mem' a := by
    refine ⟨0, 1, by simp [Submodule.one_eq_range], one_ne_zero, ?_⟩
    rw [pow_zero, mul_one]
    exact Submodule.algebraMap_mem a
  inv_mem' := by
    rintro x ⟨e, q, hq, hq0, hxq⟩
    by_cases hx : x = 0
    · subst hx
      exact ⟨e, q, hq, hq0, by simpa using hxq⟩
    · refine ⟨e, x * q, hxq, mul_ne_zero hx hq0, ?_⟩
      rwa [show x⁻¹ * (x * q) = q by field_simp]

theorem ratioField_le_sameDegQuot (ev : V →ₗ[K] Ω) : ratioField ev ≤ sameDegQuot ev := by
  rw [ratioField, IntermediateField.adjoin_le_iff]
  rintro a ⟨v, w, rfl⟩
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact (sameDegQuot ev).zero_mem
  · refine ⟨1, ev w, by simp, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]
    exact LinearMap.mem_range_self ev v

theorem isRatio_of_genRatios (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) : GenRatios ev → ∀ (τ : ℕ) (t : Ω), IsRatio ev τ t := by
  rintro ⟨hev, htop⟩ τ t
  obtain ⟨w, hw⟩ : ∃ w, ev w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hev (LinearMap.ext h)
  have hmem : t / ev w ^ τ ∈ sameDegQuot ev := by
    apply ratioField_le_sameDegQuot ev
    rw [htop]; trivial
  obtain ⟨e, q, hq, hq0, hp⟩ := hmem
  refine ⟨e, q, hq, hq0, ?_⟩
  have : t * q = (t / ev w ^ τ * q) * ev w ^ τ := by
    field_simp
  rw [this, add_comm, pow_add]
  exact Submodule.mul_mem_mul hp (Submodule.pow_mem_pow _ (LinearMap.mem_range_self ev w) τ)

end

end GlobalTheory.DegVal
