import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResBadNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResFibreFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResFibreSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ComponentResInt.proof (h₁ : ComponentResBadNull.Statement) (h₂ : ComponentResFibreFinite.Statement)
    (h₃ : ComponentResFibreSum.Statement) : ComponentResInt.Statement := by
  intro K _ _ ι _ P e L W hP hL hW hR
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P e hP
  unfold ptsIntegral GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.zInt
  rw [dif_pos hex, dif_pos hR]
  set Ψ := hex.choose with hΨdef
  have hΨ : IsGoodProj P Ψ := hex.choose_spec
  set R := hR.some with hRdef
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res.int
  have hpot : ∀ j, ReciprocityTheory.AnForm.M.IsPotential R.atlas
      (R.pot (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.logH (L j))) := fun j =>
    R.isPotential_pot (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isSmoothPot_logH
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isSmoothMetric_of_isSmoothHerm W (L j) (hL j)))
  have hgood : ∀ x ∉ resBad R Ψ, ∀ j, x ∈ (R.atlas.chart j).source →
      AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) ∧
        LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
    intro x hx j hj
    by_contra h
    exact hx (Or.inr ⟨j, hj, h⟩)
  rw [pushForward_null R.atlas _ hpot (resProj R Ψ) (resBad R Ψ) (h₁ K ι P e W R Ψ hP hW hΨ) hgood
    (h₂ K ι P e W R Ψ hP hW hΨ) _ (ReciprocityTheory.AnForm.M.mIntegrableCont R.atlas _ hpot _ continuous_const)]
  refine integral_congr_ae ?_
  filter_upwards [h₃ K ι P e L W R Ψ hP hL hW hΨ] with y hy
  rw [hy]
  exact finsum_mem_congr rfl fun x _ => (one_mul _).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
