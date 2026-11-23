import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem dadj_combination : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (n : ℕ) (u : Fin n → F), ∀ v ∈ Algebra.adjoin k (Set.range u), ∃ c : Fin n → F, (∀ j, c j ∈ Algebra.adjoin k (Set.range u)) ∧ D k K (algebraMap F K v) = ∑ j, algebraMap F K (c j) • D k K (algebraMap F K (u j)) := by
  intro k F K _ _ _ _ _ _ _ n u v hv
  induction hv using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using Subalgebra.one_mem _
      · simpa [Pi.single_apply, h] using Subalgebra.zero_mem _
    · simp [Pi.single_apply]
  | algebraMap r =>
    refine ⟨0, fun _ => Subalgebra.zero_mem _, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap]
    simp
  | add x y hx hy ihx ihy =>
    obtain ⟨cx, hcx, ex⟩ := ihx
    obtain ⟨cy, hcy, ey⟩ := ihy
    refine ⟨cx + cy, fun j => add_mem (hcx j) (hcy j), ?_⟩
    simp only [map_add, ex, ey, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | mul x y hx hy ihx ihy =>
    obtain ⟨cx, hcx, ex⟩ := ihx
    obtain ⟨cy, hcy, ey⟩ := ihy
    refine ⟨fun j => x * cy j + y * cx j, fun j => add_mem (mul_mem hx (hcy j)) (mul_mem hy (hcx j)), ?_⟩
    rw [map_mul, Derivation.leibniz, ex, ey]
    simp only [Finset.smul_sum, smul_smul, map_add, map_mul, add_smul, Finset.sum_add_distrib]

end GlobalTheory
