import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsExactIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LinearIndependentOfDetGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersNeZero

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Coords

variable {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem pb_coords (x : ι → V) (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) {v : V}
    (hv : v ∈ pbLat x 𝔞) : ∃ c : ι → K, (∀ i, c i ∈ 𝔞 i) ∧ v = ∑ i, c i • x i := by
  unfold pbLat at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, c, hc, rfl⟩ := hy
    refine ⟨Pi.single i c, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact hc
      · rw [Pi.single_eq_of_ne hj]
        exact (𝔞 j : Submodule (𝓞 K) K).zero_mem
    · symm
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  | zero => exact ⟨0, fun i => (𝔞 i : Submodule (𝓞 K) K).zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    exact ⟨c + d, fun i => (𝔞 i : Submodule (𝓞 K) K).add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  | smul r y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨fun i => algebraMap (𝓞 K) K r * c i, fun i => ?_, ?_⟩
    · have hm := Submodule.smul_mem (𝔞 i : Submodule (𝓞 K) K) r (hc i)
      rwa [Algebra.smul_def] at hm
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, algebraMap_smul]

theorem coords_unique {x : ι → V} (hind : LinearIndependent K x) {c d : ι → K}
    (h : ∑ i, c i • x i = ∑ i, d i • x i) : c = d := by
  have h0 : ∑ i, (c - d) i • x i = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have hz := Fintype.linearIndependent_iff.mp hind (c - d) h0
  funext i
  exact sub_eq_zero.mp (hz i)

end Coords

theorem sStable_prod {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} (s : Finset ι)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (h : ∀ i, SStable (𝔞 i)) : SStable (∏ i ∈ s, 𝔞 i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact sStable_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact sStable_mul (h j) ih

end PI.UnitaryGroupMassFormula.CntFormula.R6
