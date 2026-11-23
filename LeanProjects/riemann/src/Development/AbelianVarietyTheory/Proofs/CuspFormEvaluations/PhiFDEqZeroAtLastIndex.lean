import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqGeAndPhiEqZeroDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusWithSignUniformisationFrameStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem phiFD_eq_zero_at_last_index : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), j = D.R.m → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp), ∀ x ∈ ((T.U j σ).X k).dom, I2.phiFD ((T.U j σ).X k) (I2.th (E := D.host.E) q R0) x = 0 := by
  intro D T h j hj hjm DF q R0 hrun σ hσ k x hx
  have hu := h.unf j hj σ hσ
  have hq0 : (T.Q.Dw j).q = 0 := by
    rw [(h.pins.2.2.2 j hj).2.1, hjm]
    exact Nat.sub_self _
  have hp0 : ((T.U j σ).X k).p0 = 0 := ((hu.2.1 k).1).trans hq0
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hu k ⟨x, hx⟩
  have hint : ∀ u ∈ ((T.U j σ).X k).Λ, ∀ v ∈ ((T.U j σ).X k).Λ, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (((T.U j σ).X k).ξ0 * FD.herm ((T.U j σ).X k).Gm u v) = z := by
    intro u hu' v hv'
    have hEF := W.isom k ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)
    simp only [LinearEquiv.apply_symm_apply] at hEF
    refine ⟨-((W.F.Di (W.ik k)).EF ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)), ?_⟩
    rw [Int.cast_neg, hEF, neg_mul, map_neg, neg_neg]
  obtain ⟨A, -⟩ := GlobalTheory.T.exists_torusWithSign_uniformisationFrame _ _ _ _ _ _ _ _ (T.U j σ) k ⟨x, hx⟩ W
  obtain ⟨τ0⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((T.U j σ).X k).Ψ := by
    by_cases h1 : τ0 ∈ ((T.U j σ).X k).Ψ
    · exact ⟨τ0, h1⟩
    · refine ⟨NumberField.ComplexEmbedding.conjugate τ0, ?_⟩
      rw [((T.U j σ).X k).cmType]
      simpa using h1
  have hpos := A.dim_pos ⟨τ, hτ⟩
  have hneg := A.dim_neg ⟨τ, hτ⟩
  have hsum := A.T.dim_conj τ
  have hr : A.T.r = D.R.r := by
    simp only at hpos hneg
    omega
  obtain ⟨P, hPq, hPR, -⟩ := hrun A.T hr ⟨τ, by simp only at hpos; omega⟩
  have hr0 : 0 < D.R.r := by
    have h2m := D.R.two_le_m
    show 0 < D.R.k + D.R.m - 1
    omega
  refine (GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero D.host.E D.R.r ((T.U j σ).X k) hr0 hp0 hint x hx).2 q R0
    ?_ ?_ ?_
  · have h16 := P.hrd
    linarith
  · have h1q := P.hq
    omega
  · have hb := P.C2
    rwa [hPq, hPR] at hb

end GlobalTheory
