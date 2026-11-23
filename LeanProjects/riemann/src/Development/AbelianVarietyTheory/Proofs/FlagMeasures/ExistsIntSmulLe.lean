import Mathlib

namespace GlobalTheory.IntegerMultipleIntegral

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (k : K) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K a = M • k := by
  have h1 : IsAlgebraic ℚ k := Algebra.IsAlgebraic.isAlgebraic k
  have h2 : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr h1
  obtain ⟨M, hM, hint⟩ := h2.exists_integral_multiple
  exact ⟨M, hM, ⟨M • k, hint⟩, rfl⟩

theorem exists_int_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (x : V) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ A := by
  have hx : x ∈ Submodule.span K (A : Set V) := by rw [hA]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨N, hN, hz⟩ := hz
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.toAddSubgroup.zsmul_mem hy N
    · rw [mul_smul]; exact A.toAddSubgroup.zsmul_mem hz M
  | smul k y _ hy =>
    obtain ⟨N, hN, hy⟩ := hy
    obtain ⟨M, hM, a, ha⟩ := exists_int_mul_integral k
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have : (M * N) • k • y = a • (N • y) := by
      rw [← algebraMap_smul K a, ha, smul_assoc, mul_smul, smul_comm N k y]
    rw [this]
    exact A.smul_mem a hy

theorem exists_int_smul_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    {B : Submodule (NumberField.RingOfIntegers K) V} (hB : B.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ B, N • x ∈ A := by
  obtain ⟨s, rfl⟩ := hB
  choose f hf0 hf using exists_int_smul_mem hA
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr fun y _ => hf0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hy)
    rw [hc, mul_comm, mul_smul]
    exact A.toAddSubgroup.zsmul_mem (hf y) c
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact A.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact A.smul_mem a hy

end GlobalTheory.IntegerMultipleIntegral
