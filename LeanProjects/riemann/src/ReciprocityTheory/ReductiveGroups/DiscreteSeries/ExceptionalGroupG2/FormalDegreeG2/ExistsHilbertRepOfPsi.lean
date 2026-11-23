import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.ImportsAlt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem exists_hilbert_rep_of_psi :
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), StdGap ε lam → IsPsiFor ε lam T Ψ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
      IsHWSmooth ε σ lam w ∧ ∀ g ∈ UJset ε, ⟪w, σ g w⟫_ℂ = ⟪T.w, Ψ g T.w⟫_ℂ := by
  intro n ε lam T Ψ hgap hP
  have hv₀ : T.w ≠ 0 := by
    intro h
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hgap hP hv₀)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have h0 : uniformisationL2 ε Ψ T.w 0 = 0 := by simpa using datumEmbedding_smul hP T.w 0 T.w
  have hmem := datumEmbedding_mem_smooth hP T.w (c • T.w)
  refine ⟨L2 ε, inferInstance, inferInstance, rreg ε, uniformisationL2 ε Ψ T.w (c • T.w), ?_, ?_⟩
  · refine ⟨rreg_isURepOn ε, hmem, ?_, ?_, ?_⟩
    · rw [datumEmbedding_smul hP, norm_smul, hc, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hN0]
    · constructor
      · intro a
        apply Subtype.ext
        rw [rightDerivative_datum_embedding hP T.w (c • T.w) rfl, map_smul, T.w_wt a, Submodule.coe_smul, ← datumEmbedding_smul hP,
          smul_comm]
      · intro a b hab hε
        apply Subtype.ext
        rw [rightDerivative_datum_embedding hP T.w (c • T.w) hε, map_smul, T.w_hw a b hab hε, smul_zero, h0]
        rfl
    · exact datumV_casimir hP T.w _ ((mem_datumV_iff hP T.w _).2 ⟨c • T.w, rfl⟩)
  · intro g hg
    have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
      rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
      congr 1
      rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
    rw [formulaF hgap hP hv₀ hg (c • T.w) (c • T.w), map_smul, inner_smul_left, inner_smul_right,
      ← mul_assoc (starRingEnd ℂ c), ← mul_assoc, key, one_mul]

end ReciprocityTheory.ChartRestriction.DS.G2
