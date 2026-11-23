import Mathlib

namespace GlobalTheory.SmulMemOfMemSpanExists

theorem exists_smul_mem_of_mem_span {Oe K'' T : Type} [CommRing Oe] [IsDomain Oe] [Field K'']
    [Algebra Oe K''] [IsFractionRing Oe K''] [AddCommGroup T] [Module K'' T] [Module Oe T]
    [IsScalarTower Oe K'' T] (M : Submodule Oe T) {x : T}
    (hx : x ∈ Submodule.span K'' (↑M : Set T)) : ∃ c : Oe, c ≠ (0 : Oe) ∧ c • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hay
    · rw [mul_smul]; exact M.smul_mem _ hbz
  | smul k y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := Oe) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap Oe K'' d ≠ 0 := fun h =>
      hd0 (IsFractionRing.injective Oe K'' (by rw [h, map_zero]))
    refine ⟨a * d, mul_ne_zero ha hd0, ?_⟩
    have key : (a * d) • ((algebraMap Oe K'' n / algebraMap Oe K'' d) • y) = n • (a • y) := by
      rw [← algebraMap_smul K'' (a * d), ← algebraMap_smul K'' n, ← algebraMap_smul K'' a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem _ hay

end GlobalTheory.SmulMemOfMemSpanExists
