import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.OfIntegralHolds

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.LowestKTypeUnitIntegral

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.MainNotions.BridgeCSchur

theorem lowest_q_le_rank {m : ℕ} (ε : Fin m → Bool) : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := by
  have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ m :=
    (min_le_left _ _).trans (by unfold ReciprocityTheory.ChartRestriction.DS.pOf; exact (Finset.card_filter_le _ _).trans (by simp))
  exact_mod_cast this

theorem models_holds : Models := by
  intro n ε lam ε' mu e hG
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hG.two
  have hx3 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hx2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hbig : 2 * ((n + 1 : ℕ) : ℝ) < 200 * ((n : ℝ) + 1) ^ 3 := by push_cast; linarith
  have hbig' : 2 * (n : ℝ) < 200 * ((n : ℝ) + 1) ^ 3 := by linarith
  constructor
  · rintro ⟨H0, H0', i1, i2, i3, i4, π0, σ0, hπ0, hσ0, j0, hj00, hj0⟩ H H' _ _ _ _ _ _ π σ hπ hσ
    haveI := hπ0.1
    haveI := hσ0.1
    obtain ⟨UG, hUG⟩ := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap (n + 1) ε lam hG.hc _ hG.gap hbig H0 π0 hπ0).2.2.2.2 H π hπ
    obtain ⟨UH, hUH⟩ := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap n ε' mu hG.hc' _ hG.gap' hbig' H0' σ0 hσ0).2.2.2.2 H' σ hσ
    refine ⟨(UG : H0 →L[ℂ] H).comp (j0.comp (UH.symm : H' →L[ℂ] H0')), fun h0 => hj00 ?_, fun h x => ?_⟩
    · refine ContinuousLinearMap.ext fun y => ?_
      have := congrArg (fun f => UG.symm (f (UH y))) h0
      simpa using this
    · have e1 : UH.symm (σ (um h) x) = σ0 (um h) (UH.symm x) := by
        apply UH.injective
        rw [hUH _ (umat_mem h), LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
      simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'', ContinuousLinearEquiv.coe_coe]
      show UG (j0 (UH.symm (σ (um h) x))) = π (emb e (um h)) (UG (j0 (UH.symm x)))
      have m1 : emb e (um h) ∈ UJset ε := umat_mem (embU hG.fits h)
      rw [e1, hj0, hUG _ m1]
  · intro hO
    obtain ⟨H, i1, i2, π, hπ⟩ := ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap (n + 1) ε lam hG.hc _ hG.gap (Or.inr (by
      have := lowest_q_le_rank ε
      refine max_lt hbig ?_
      push_cast at this ⊢
      have h1 : 8 * ((n : ℝ) + 1) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith))
    obtain ⟨H', i1', i2', σ, hσ⟩ := ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap n ε' mu hG.hc' _ hG.gap' (Or.inr (by
      have := lowest_q_le_rank ε'
      refine max_lt hbig' ?_
      have h1 : 8 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε' : ℝ) ≤ 8 * (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith))
    haveI := hπ.1
    haveI := hσ.1
    exact ⟨H, H', i1, i2, i1', i2', π, σ, hπ, hσ, hO H H' π σ hπ hσ⟩

end PositivityTheory.RgHe.LowestKTypeUnitIntegral
