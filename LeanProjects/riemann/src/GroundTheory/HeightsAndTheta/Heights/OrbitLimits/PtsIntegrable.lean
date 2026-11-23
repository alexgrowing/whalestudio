import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSumMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem abs_finsum_mem_le_finsum_mem_abs {α : Type*} (S : Set α) (f : α → ℝ) :
    |∑ᶠ w ∈ S, f w| ≤ ∑ᶠ w ∈ S, |f w| := by
  rw [finsum_mem_def, finsum_mem_def]
  have hind : S.indicator (fun w => |f w|) = fun w => |S.indicator f w| := by
    funext w
    by_cases hw : w ∈ S <;> simp [hw]
  rw [hind]
  have hsupp : Function.support (fun w => |S.indicator f w|) = Function.support (S.indicator f) := by
    ext w
    simp
  by_cases hfin : (Function.support (S.indicator f)).Finite
  · have hfin' : (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_eq_sum _ hfin, finsum_eq_sum _ hfin']
    have hs : hfin'.toFinset = hfin.toFinset := by
      ext w
      simp only [Set.Finite.mem_toFinset, hsupp]
    rw [hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · have hinf' : ¬ (Function.support (fun w => |S.indicator f w|)).Finite := hsupp ▸ hfin
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support hinf', abs_zero]

theorem PtsIntegrable.of_found (hAbs : Inter.PtsAbsIntegrable.Statement)
    (hMeas : PtsSumMeasurable.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  refine (hAbs K ι P e Ψ L A s hP hΨ hL hA hs).mono' (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact abs_finsum_mem_le_finsum_mem_abs _ _

end GroundTheory.Heights₂.Heights
