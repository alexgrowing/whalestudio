import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem prod_sec_pow_mul_mem {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j) (α : Fin (WeightFamilies.dimY D j) → ℕ) (s : Finset (Fin (WeightFamilies.dimY D j)))
    {n : ℕ} {v : Rp X la N} (hv : v ∈ Vw X la N (addL u wL n)) :
    (∏ i ∈ s, sec X la w i.succ ^ α i) * v ∈ Vw X la N (addL u wL (n + ∑ i ∈ s, α i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using hv
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have := sec_pow_mul_mem X la w a.succ u _ (α a) ih
    rwa [show n + ∑ i ∈ s, α i + α a = n + (α a + ∑ i ∈ s, α i) by ring] at this

theorem taylorSpanGenerators : TaylorSpanGenerators := by
  intro D B P j X ka wL wF G la T k hk α hα i
  have hs : ∑ i, α i = k := Finset.Nat.mem_antidiagonalTuple.1 hα
  have hkT : ∑ i, α i ≤ T := by
    have : a0 D j T ≤ T := Nat.sub_le _ _
    omega
  have h0 : emb X la G.N (X.inc wF (G.th' i)) ∈ Vw X la G.N (addL wF wL 0) := by
    rw [addL_zero]; exact emb_mem_Vw X la G.N wF _
  have h1 := sec_pow_mul_mem X la G.w 0 wF 0 (T - ∑ i, α i) h0
  have h2 := prod_sec_pow_mul_mem G.w wF α Finset.univ h1
  rw [show 0 + (T - ∑ i, α i) + ∑ i, α i = T by omega] at h2
  have hf : secPow X la G.w α * sec X la G.w 0 ^ (T - ∑ i, α i) * emb X la G.N (X.inc wF (G.th' i)) ∈
      Vw X la G.N (addL wF wL T) := by
    rw [mul_assoc]; exact h2
  refine ⟨toHK X la G.w wF T ⟨_, hf⟩,
    toHK0 X la G.w wF ⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩, ?_, ?_, rfl⟩
  · exact Submodule.subset_span ⟨⟨_, hf⟩, ⟨α, i, by omega, rfl⟩, rfl⟩
  · apply Subtype.ext
    have e1 : ((ym G la α : ↥(Frac0 X la G.w)) : Lw X la G.w) = frac X la G.w (∑ i, α i) (secPow X la G.w α) :=
      coe_prod_sfr X la G.w α
    rw [Submodule.coe_smul, Subalgebra.smul_def, smul_eq_mul, e1, coe_toHK, coe_toHK0, ← frac_zero, frac_mul,
      add_zero]
    have e2 := frac_pow_mul X la G.w (∑ i, α i) (T - ∑ i, α i)
      (secPow X la G.w α * emb X la G.N (X.inc wF (G.th' i)))
    rw [show ∑ i, α i + (T - ∑ i, α i) = T by omega] at e2
    rw [← e2]
    congr 1
    show _ = _
    ring

end PoleLengthBounds
