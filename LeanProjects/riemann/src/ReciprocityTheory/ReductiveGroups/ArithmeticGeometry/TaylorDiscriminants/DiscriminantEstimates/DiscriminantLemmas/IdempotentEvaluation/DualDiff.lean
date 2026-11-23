import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen

namespace PI.UnitaryGroupMassFormula.TBIdemDen

open ReciprocityTheory.ChartRestriction.G.TB NumberField TensorProduct

theorem dualDiff : DualDiffSt := by
  intro E _ _ ι _ _ b _ hspan δ hδ i
  have key : ∀ j, Algebra.traceForm ℚ E (trDual b i) (b j) = if j = i then 1 else 0 := by
    intro j
    unfold trDual
    first
      | exact LinearMap.BilinForm.apply_dualBasis_left _ _ _ _ _
      | simp [LinearMap.BilinForm.apply_dualBasis_left]
      | simp [LinearMap.BilinForm.dualBasis]
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
    intro h
    have h1 : (1 : E) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    rw [h, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  have hy : trDual b i ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨c, hc⟩ := hspan x
    refine ⟨c i, ?_⟩
    have hx : algebraMap (𝓞 E) E x = ∑ k, (c k : ℚ) • b k := hc
    rw [hx, map_sum]
    simp only [map_smul, key, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, eq_intCast]
  have hd : (δ : E) ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
    rw [← coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)]
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 E)) hδ
  have hm := FractionalIdeal.mul_mem_mul hd hy
  rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)] at hm
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  rw [← hz]
  exact z.isIntegral_coe

end PI.UnitaryGroupMassFormula.TBIdemDen
