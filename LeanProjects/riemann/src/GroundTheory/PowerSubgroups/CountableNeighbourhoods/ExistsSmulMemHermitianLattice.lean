import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice

namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_smul_mem_hermitianLattice {K : Type} [Field K] [NumberField K] {i : ℕ}
    (X : GroundTheory.Heights₂.Heights.HermLattice K i) (v : Fin i → K) :
    ∃ (c : NumberField.RingOfIntegers K), c ≠ 0 ∧ c • v ∈ X.lattice := by
  have hv : v ∈ Submodule.span K (X.lattice : Set (Fin i → K)) := by
    rw [X.span_eq]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact X.lattice.add_mem (X.lattice.smul_mem _ hax) (X.lattice.smul_mem _ hby)
  | smul k x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (𝓞 K) K q ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) • x) = p • (a • x) := by
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def (R := 𝓞 K) (A := K), map_mul]
      field_simp
    rw [key]
    exact X.lattice.smul_mem _ hax

end GroundTheory.Variant₂.N1
