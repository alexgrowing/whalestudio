import Mathlib

namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_smul_mem_of_span_eq_top {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (RingOfIntegers K) (Fin N → K))
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤) (x : Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ algebraMap (RingOfIntegers K) K t • x ∈ M := by
  have hx : x ∈ Submodule.span K (M : Set (Fin N → K)) := by rw [hM]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have h1 : algebraMap (RingOfIntegers K) K (s * t) • y
        = t • (algebraMap (RingOfIntegers K) K s • y) := by
      rw [map_mul, mul_comm, mul_smul, algebraMap_smul]
    have h2 : algebraMap (RingOfIntegers K) K (s * t) • z
        = s • (algebraMap (RingOfIntegers K) K t • z) := by
      rw [map_mul, mul_smul, algebraMap_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (M.smul_mem t hsy) (M.smul_mem s htz)
  | smul c y _ hy =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    refine ⟨(b : RingOfIntegers K) * t, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) ht, ?_⟩
    have key : algebraMap (RingOfIntegers K) K ((b : RingOfIntegers K) * t) • (c • y)
        = a • (algebraMap (RingOfIntegers K) K t • y) := by
      rw [← algebraMap_smul K a (algebraMap (RingOfIntegers K) K t • y), smul_smul, smul_smul,
        ← hab, map_mul]
      congr 1
      ring
    rw [key]
    exact M.smul_mem a hty

theorem exists_smul_mem_family_of_span_eq_top {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (RingOfIntegers K) (Fin N → K))
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ ∀ i, algebraMap (RingOfIntegers K) K t • v i ∈ M := by
  classical
  choose s hs hsv using fun i => exists_smul_mem_of_span_eq_top M hM (v i)
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.mpr fun i _ => hs i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), mul_comm, map_mul, mul_smul,
    algebraMap_smul]
  exact M.smul_mem _ (hsv i)

end GroundTheory.Variant₂.N1
