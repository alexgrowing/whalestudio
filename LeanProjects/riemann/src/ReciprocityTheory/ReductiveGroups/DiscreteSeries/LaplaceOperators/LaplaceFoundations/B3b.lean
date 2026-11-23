import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem b3b : DerivMatrixCoeffExp := by
  intro n ε H _ _ σ w hσ hw Z hZ s
  have h0 := (isDerivedOn_smE hσ).deriv Z hZ ⟨w, hw⟩
  have hphi : phiW ε σ w Z = ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    simp only [phiW, dif_pos hw]
  set g := σ (NormedSpace.exp ((s : ℂ) • Z)) with hg
  set T : H →L[ℂ] ℂ := (innerSL ℂ w).comp g with hT
  have h1 := ((T.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h0
  have h2 : HasDerivAt (fun x : ℝ => T (σ (NormedSpace.exp (((x - s : ℝ) : ℂ) • Z)) w))
      (T ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) s := by
    have h1' : HasDerivAt (⇑(ContinuousLinearMap.restrictScalars ℝ T) ∘
        fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • Z))) w)
        ((ContinuousLinearMap.restrictScalars ℝ T) ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) (s - s) := by
      rw [sub_self]; exact h1
    exact h1'.comp_sub_const s s
  rw [hphi]
  convert h2 using 1
  · funext x
    have he : NormedSpace.exp ((x : ℂ) • Z) =
        NormedSpace.exp ((s : ℂ) • Z) * NormedSpace.exp (((x - s : ℝ) : ℂ) • Z) := by
      rw [← exp_add_smul]
      congr 2
      push_cast
      ring
    rw [he, hσ.1.2 _ (exp_smul_mem_UJset hZ s) _ (exp_smul_mem_UJset hZ (x - s))]
    simp [hT, hg]
  · simp [hT, hg]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
