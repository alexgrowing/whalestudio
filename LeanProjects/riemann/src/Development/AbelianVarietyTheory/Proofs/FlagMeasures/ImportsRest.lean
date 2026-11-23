import Mathlib

namespace GlobalTheory.SmulMemSpan

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (x : V) :
    ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have key : (d * a) • ((algebraMap (NumberField.RingOfIntegers K) K n /
        algebraMap (NumberField.RingOfIntegers K) K d) • y) = n • (a • y) := by
      have hdK : algebraMap (NumberField.RingOfIntegers K) K d ≠ 0 := by
        simpa using hd0
      rw [← algebraMap_smul K (d * a), smul_smul, ← algebraMap_smul K n, ← algebraMap_smul K a,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact L.smul_mem n hay

end GlobalTheory.SmulMemSpan
