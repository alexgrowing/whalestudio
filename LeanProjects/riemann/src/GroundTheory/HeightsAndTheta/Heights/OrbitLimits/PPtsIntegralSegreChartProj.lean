import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralSegreChartProj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartProjFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSegreChartFibreSum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (ptsIntegralAt)
open ComplexSets

theorem PtsIntegralSegreChartProj.proof (hFin : SegreChartProjFinite.Statement)
    (hZero : SegreChartZeroSet.Statement) (hAbs : SegreChartAbsIntegrable.Statement)
    (hSum : PtsSegreChartFibreSum.Statement) : PtsIntegralSegreChartProj.Statement := by
  intro K _ _ ι _ P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  set A := chartProjMatrix σ Ψ
  set G' := chartWeight σ i g with hG'
  set Φ' := chartPot σ i L
  have hcoordS : ∀ x ∈ segreChartSet P σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hchart : ∀ J ∈ segreChartComponents P σ i, zeroSet J ⊆ segreChartSet P σ i := by
    intro J hJ x hx
    rw [← hZero K ι P m σ i hP.2.1.2.1]
    exact fun q hq => hx q ((mem_segreChartComponents.1 hJ).1.2 hq)
  have hprime : ∀ J ∈ segreChartComponents P σ i, J.IsPrime := fun J hJ =>
    (mem_segreChartComponents.1 hJ).1.1
  have hdim : ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) := fun J hJ =>
    SegreChartDim.proof K ι P (e + 1) m σ i hP J hJ
  have hfin : ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J A :=
    hFin K ι P (e + 1) m σ i Ψ hP hΨ hΨ0
  have hmeas : Measurable G' := measurable_chartWeight σ i hg
  have hsm : ∀ J ∈ segreChartComponents P σ i, ∀ k, SmoothNear (zeroSet J) (Φ' k) := fun J hJ =>
    smoothNear_chartPot σ i hL fun x hx => chart_coord_eq_one hJ hx
  have habs : ∀ J ∈ segreChartComponents P σ i, Integrable (chartAbsDens J A G' Φ') := fun J hJ =>
    hAbs K ι P (e + 1) m σ i L g hP hL hg J hJ A (hfin J hJ)
  have hint : ∀ J ∈ segreChartComponents P σ i, Integrable (chartDens J A G' Φ') := by
    intro J hJ
    refine (habs J hJ).mono' (SheetSumMeasurable.full m (e + 1) J A G' Φ' (hprime J hJ) (hdim J hJ)
      (hfin J hJ) hmeas (hsm J hJ)).1.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens sheetSum
    refine (abs_finsum_mem_le_finsum_mem_abs _ _).trans (le_of_eq (finsum_mem_congr rfl fun x _ => ?_))
    split_ifs <;> simp

  have hcong : ∀ J ∈ segreChartComponents P σ i, ∀ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ,
      chartDens J A₁ G Φ = chartDens J A₁ G' Φ' := by
    intro J hJ A₁
    funext y
    unfold chartDens sheetSum
    refine finsum_mem_congr rfl fun x hx => ?_
    have hxS : x ∈ segreChartSet P σ i := hchart J hJ hx.1
    split_ifs with h
    · obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := h.choose_spec
      have hy : A₁ *ᵥ x = y := hx.2
      have hG : G x = G' x := by
        rw [hG', chartWeight_of_coord g (hcoordS x hxS)]
        exact (hgerm x hxS).1.eq_of_nhds
      have hcont : Tendsto h.choose (𝓝 y) (𝓝 x) := by
        have := (hdiff.continuousOn.continuousAt (hU.mem_nhds hyU)).tendsto
        rwa [hsx, hy] at this
      beta_reduce
      rw [hG]
      congr 1
      exact ReciprocityTheory.AnForm.M.maDens_congr_eventuallyEq fun k => ((hgerm x hxS).2 k).comp_tendsto hcont
    · rfl

  have hvar : ∀ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ = ∫ y, chartDens J A G' Φ' y := by
    intro J hJ
    have hex : ∃ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ, IsFiniteProjection J A₁ := ⟨A, hfin J hJ⟩
    rw [varInt, dif_pos hex, chartInt, hcong J hJ]
    exact (IntegralIndep.full m (e + 1) J A hex.choose G' Φ' (hprime J hJ) (hdim J hJ) (hfin J hJ)
      hex.choose_spec hmeas (hsm J hJ) (habs J hJ)).2.symm
  rw [Finset.sum_congr rfl hvar, ← integral_finsetSum _ hint]
  unfold ptsIntegralAt
  refine integral_congr_ae ?_
  filter_upwards [hSum K ι P (e + 1) m σ i L g Ψ hP hL hg hΨ hΨ0] with y hy
  exact hy

end GroundTheory.Heights₂.Heights
