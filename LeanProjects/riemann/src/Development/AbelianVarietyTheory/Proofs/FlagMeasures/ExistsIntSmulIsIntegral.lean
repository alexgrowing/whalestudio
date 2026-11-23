import Mathlib

namespace GlobalTheory.IntSmulIsIntegral

theorem exists_int_smul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a) := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  exact h.exists_integral_multiple

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (M : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (hM : Submodule.span E (↑M : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • x ∈ M := by
  have hx : x ∈ Submodule.span E (↑M : Set (Fin n → E)) := hM ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have e : (c * d) • (y + z) = d • (c • y) + c • (d • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm d c]
    rw [e]
    exact M.add_mem (zsmul_mem hcy d) (zsmul_mem hdz c)
  | smul a y _ hy =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨d, hd, hda⟩ := exists_int_smul_isIntegral a
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    have h := M.smul_mem (⟨d • a, hda⟩ : NumberField.RingOfIntegers E) hcy
    have e : (d * c) • (a • y) =
        (⟨d • a, hda⟩ : NumberField.RingOfIntegers E) • (c • y) := by
      change _ = (d • a) • (c • y)
      rw [smul_assoc, smul_comm a c y, smul_smul d c]
    rw [e]
    exact h

end GlobalTheory.IntSmulIsIntegral
