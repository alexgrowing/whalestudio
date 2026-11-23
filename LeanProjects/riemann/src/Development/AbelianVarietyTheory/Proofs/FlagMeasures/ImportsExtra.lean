import Mathlib

namespace GlobalTheory.ClearingDenominatorsInOrder

theorem main {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (NumberField.RingOfIntegers E) W]
    [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W) :
    ∀ v ∈ Submodule.span E (↑L : Set W),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ L := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, hc1, h1⟩ := hx
    obtain ⟨c2, hc2, h2⟩ := hy
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add]
    apply L.add_mem
    · rw [mul_comm, mul_smul]; exact L.smul_mem c2 h1
    · rw [mul_smul]; exact L.smul_mem c1 h2
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    simp only at hnd
    have hd : (d : NumberField.RingOfIntegers E) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have key : (d : NumberField.RingOfIntegers E) • (a • x) = n • x := by
      rw [← algebraMap_smul E (d : NumberField.RingOfIntegers E), smul_smul, mul_comm, hnd,
        algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact L.smul_mem n h

end GlobalTheory.ClearingDenominatorsInOrder
