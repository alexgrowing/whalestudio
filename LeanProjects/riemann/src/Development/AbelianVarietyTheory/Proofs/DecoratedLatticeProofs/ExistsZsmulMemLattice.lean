import Mathlib

namespace GlobalTheory.LatticeIntegerMultiple

open NumberField

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (m : ℤ) (b : RingOfIntegers E), m ≠ 0 ∧ algebraMap (RingOfIntegers E) E b = m • a := by
  have hQ : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have hZ : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hQ
  obtain ⟨m, hm, hi⟩ := hZ.exists_integral_multiple
  exact ⟨m, ⟨m • a, hi⟩, hm, rfl⟩

theorem exists_zsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) [Submodule.IsLattice E L] (x : Fin n → E) :
    ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [Submodule.IsLattice.span_eq_top (A := E)]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨k, hk, hz⟩ := hz
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hy k
    · rw [mul_smul]; exact zsmul_mem hz m
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨k, b, hk, hb⟩ := exists_int_mul_mem a
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have h : (k * m) • a • y = b • (m • y) := by
      rw [← algebraMap_smul E b, hb, mul_smul, smul_comm m a y, smul_assoc]
    rw [h]
    exact L.smul_mem b hy

end GlobalTheory.LatticeIntegerMultiple
