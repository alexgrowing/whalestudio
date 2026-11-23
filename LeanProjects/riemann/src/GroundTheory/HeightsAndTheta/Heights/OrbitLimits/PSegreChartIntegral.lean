import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreCoordGoodProj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralProjIndep
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralSegreChartProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegral
  ptsIntegralAt sheetDensity fibre maDensity mixedDisc cxHessian pot segre mcPts goodProjExists)

theorem maDensity_eq_zero_of_eventuallyEq_zero {D : ℕ} (φ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    (y : Fin (D + 1) → ℂ) (h : φ 0 =ᶠ[𝓝 y] 0) : maDensity φ y = 0 := by
  have hH : fderiv ℝ (fderiv ℝ (φ 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]
    simp
  have hC : cxHessian (φ 0) y = 0 := by
    ext a b
    simp [cxHessian, hH]
  have hU : (fun k => cxHessian (φ k) y) =
      Function.update (fun k => cxHessian (φ k) y) 0 ((0 : ℂ) • (0 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [hC]
    · simp [Function.update_of_ne hk]
  have hM : mixedDisc (fun k => cxHessian (φ k) y) = 0 := by
    have hdef : mixedDisc (fun k => cxHessian (φ k) y) = ReciprocityTheory.AnForm.mdisc (fun k => cxHessian (φ k) y) :=
      rfl
    rw [hdef, hU, ReciprocityTheory.AnForm.A.mdisc_update_smul, zero_mul]
  simp [maDensity, hM]

theorem SegreChartIntegral.proof (hGood : SegreCoordGoodProj.Statement)
    (hIndep : PtsIntegralProjIndep.Statement) (hChart : PtsIntegralSegreChartProj.Statement) :
    SegreChartIntegral.Statement := by
  classical
  intro K _ _ ι _ P e m σ i L g δ G Φ hP hL hg hδ hsupp hgerm
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P (e + 1) hP
  have hpts : ptsIntegral P (pot L) g = ptsIntegralAt P hex.choose (pot L) g := by
    unfold ptsIntegral
    rw [dif_pos hex]
  rw [hpts]
  by_cases hne : ∃ z ∈ mcPts P, segre z i ≠ 0
  · obtain ⟨Ψ, hΨ, hΨ0⟩ := hGood K ι P (e + 1) i hP hne
    rw [hIndep K ι P (e + 1) _ Ψ L g hP hex.choose_spec hΨ hL hg]
    exact hChart K ι P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  · push Not at hne

    have hset : segreChartSet P σ i = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, hzi, -⟩
      rw [hne z hz] at hzi
      exact zero_ne_one hzi
    have hcomp : segreChartComponents P σ i = ∅ := by
      ext J
      simp only [mem_segreChartComponents, Finset.notMem_empty, iff_false]
      intro hJ
      have htop : segreChartIdeal P σ i = ⊤ := by
        rw [segreChartIdeal, hset]
        exact MvPolynomial.vanishingIdeal_empty
      rw [htop] at hJ
      exact hJ.1.1.ne_top (top_le_iff.1 hJ.1.2)
    rw [hcomp, Finset.sum_empty]

    have hin : ∀ z ∈ mcPts P, ‖segre z i‖ < δ * ‖segre z‖ := by
      intro z hz
      rw [hne z hz, norm_zero]
      choose j hj using hz.1
      have hj' : segre z j ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hj k
      exact mul_pos hδ (norm_pos_iff.2 fun h0 => hj' (congrFun h0 j))
    have hterm : ∀ y w, sheetDensity P hex.choose (pot L) g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · have hs : IsSheet P hex.choose y w hγ.choose := hγ.choose_spec
        rcases hsupp with hg0 | hp0
        · rw [hg0 _ (hin _ hs.2.self_of_nhds.2.1), zero_mul]
        · rw [maDensity_eq_zero_of_eventuallyEq_zero _ _ ?_, mul_zero]
          filter_upwards [hs.2] with y' hy'
          exact hp0 _ (hin _ hy'.2.1)
      · rfl
    unfold ptsIntegralAt
    simp [hterm]

end GroundTheory.Heights₂.Heights
