import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem HodgeFibreSpan.proof : HodgeFibreSpan.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D τ bfr b' R R' Rz R'z z hz hbfr hb' hF hR hR' hRz hR'z
  have hj : (jIdx D : ℕ) + 1 = D.j := by
    have := D.one_le_j
    simp only [jIdx]
    omega

  have hRR : ∀ k i, ∑ q, R' k q * R q i = if k = i then 1 else 0 := by
    intro k i
    refine Fintype.linearIndependent_iffₛ.mp hb' (fun k => ∑ q, R' k q * R q i)
      (fun k => if k = i then 1 else 0) ?_ k
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hR i]
    simp_rw [hR', Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨e, he, c, rfl, hcv⟩
    rw [← hF, Finsupp.mem_span_image_iff_linearCombination] at he
    obtain ⟨l, hl, hle⟩ := he
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hle

    have hc : ∀ q, c q = ∑ i, R q i * l i := by
      intro q
      refine Fintype.linearIndependent_iffₛ.mp hbfr c (fun q => ∑ i, R q i * l i) ?_ q
      rw [← hle]
      simp_rw [hR, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]

    have hl' : ∀ k, l k = ∑ q, R' k q * c q := by
      intro k
      simp_rw [hc, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hRR]
      simp
    set w : Fin D.N → ℂ := fun k => ∑ q, R'z k q * v q with hwdef
    have hw : ∀ k, IsValueAt D.y (l k) z (w k) := fun k => by
      rw [hl' k]
      exact LineFlag.isValueAt_sum _ _ fun q => LineFlag.isValueAt_mul (hR'z k q) (hcv q)
    have hw0 : ∀ k : Fin D.N, ¬ ((k : ℕ) < D.j) → w k = 0 := fun k hk => by
      have h0 := hw k
      rw [(Finsupp.mem_supported' _ _).mp hl k hk] at h0
      exact LineFlag.isValueAt_unique hz h0 (LineFlag.isValueAt_zero' _ _)
    have hv : v = ∑ i, w i • fun p => Rz p i := by
      funext p
      have h1 : IsValueAt D.y (c p) z (∑ i, Rz p i * w i) := by
        rw [hc p]
        exact LineFlag.isValueAt_sum _ _ fun i => LineFlag.isValueAt_mul (hRz p i) (hw i)
      rw [LineFlag.isValueAt_unique hz (hcv p) h1]
      simp [Finset.sum_apply, mul_comm]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < D.j
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩)
    · rw [hw0 i hi, zero_smul]
      exact Submodule.zero_mem _
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    refine ⟨b' (Fin.castLE (jIdx D).isLt a), ?_, fun q => R q (Fin.castLE (jIdx D).isLt a), hR _,
      fun q => hRz q _⟩
    rw [← hF]
    exact Submodule.subset_span ⟨_, by simp only [Set.mem_ofPred_eq, Fin.val_castLE]; omega, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
