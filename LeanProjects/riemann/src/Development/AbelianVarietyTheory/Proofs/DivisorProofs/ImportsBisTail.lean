import Mathlib

namespace GlobalTheory.UnitaryNormalization

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (B : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) :
    ∀ x ∈ Submodule.span E (↑B : Set (Fin n → E)),
      ∃ (s : NumberField.RingOfIntegers E), s ≠ (0 : NumberField.RingOfIntegers E) ∧ s • x ∈ B := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    have h1 : (s * t) • y = t • (s • y) := by rw [mul_comm, mul_smul]
    have h2 : (s * t) • z = s • (t • z) := by rw [mul_smul]
    rw [h1, h2]
    exact B.add_mem (B.smul_mem t hsy) (B.smul_mem s htz)
  | smul a y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    simp only at hpq
    refine ⟨(q : RingOfIntegers E) * s, mul_ne_zero (nonZeroDivisors.coe_ne_zero q) hs, ?_⟩
    have : ((q : RingOfIntegers E) * s) • (a • y) = p • (s • y) := by
      rw [algebra_compatible_smul E ((q : RingOfIntegers E) * s), algebra_compatible_smul E p,
        algebra_compatible_smul E s, smul_smul, smul_smul, map_mul, ← hpq]
      congr 1
      ring
    rw [this]
    exact B.smul_mem p hsy

end GlobalTheory.UnitaryNormalization
