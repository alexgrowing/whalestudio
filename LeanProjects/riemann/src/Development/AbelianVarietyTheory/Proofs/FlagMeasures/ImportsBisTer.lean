import Mathlib
open NumberField

namespace GlobalTheory.IntMulIntegral

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ M : ℤ, M ≠ 0 ∧ IsIntegral ℤ ((M : K) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem main : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V]
    [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V}, Submodule.span K (↑A : Set V) = ⊤ →
    ∀ (x : V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • x ∈ A := by
  intro K V _ _ _ _ _ _ A hA x
  have hx : x ∈ Submodule.span K (↑A : Set V) := by rw [hA]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨N₁, h₁, m₁⟩ := hy
    obtain ⟨N₂, h₂, m₂⟩ := hw
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.smul_of_tower_mem N₂ m₁
    · rw [mul_smul]; exact A.smul_of_tower_mem N₁ m₂
  | smul c y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨M, hM, hint⟩ := exists_int_mul_integral c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    let o : NumberField.RingOfIntegers K := ⟨(M : K) * c, hint⟩
    have key : (M * N) • (c • y) = o • (N • y) := by
      rw [← algebraMap_smul K o (N • y)]
      have : algebraMap (NumberField.RingOfIntegers K) K o = (M : K) * c := rfl
      rw [this, mul_smul, mul_smul, ← Int.cast_smul_eq_zsmul K M, ← Int.cast_smul_eq_zsmul K N,
        ← Int.cast_smul_eq_zsmul K N, smul_comm c ((N : K)) y]
    rw [key]
    exact A.smul_mem o m

end GlobalTheory.IntMulIntegral
