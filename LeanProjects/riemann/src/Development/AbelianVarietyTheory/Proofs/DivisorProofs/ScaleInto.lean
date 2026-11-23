import Mathlib

namespace GlobalTheory.ScaleIntoUnitBall

open NumberField

theorem scale_into {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Submodule (𝓞 K) V) {x : V}
    (hx : x ∈ Submodule.span K (W : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ W := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e1 : (d1 * d2) • y = d2 • (d1 • y) := by rw [mul_comm, mul_smul]
    have e2 : (d1 * d2) • z = d1 • (d2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact W.add_mem (W.smul_mem _ h1) (W.smul_mem _ h2)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]; exact hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have hc : b • c = algebraMap (𝓞 K) K a := by
      rw [Algebra.smul_def, ← hab, mul_div_cancel₀ _ hbK]
    have key : (b * d) • (c • y) = a • (d • y) := by
      rw [mul_comm, mul_smul, ← smul_assoc b c y, hc, algebraMap_smul, smul_comm]
    rw [key]
    exact W.smul_mem _ h

end GlobalTheory.ScaleIntoUnitBall
