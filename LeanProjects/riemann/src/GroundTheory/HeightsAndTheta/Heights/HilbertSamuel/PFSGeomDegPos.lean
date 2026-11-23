import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFSGeomDegPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreDegreeSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem FSGeomDegPos.proof (hDeg : DegreeStatement) (hPos : MultiDegreePositive.Statement) :
    FSGeomDegPos.Statement := by
  intro K _ ι _ P e hP
  classical
  have hS : ∀ j : Fin e, IsSmoothHerm ((fun _ : Fin e => fsH ι) j) := fun _ =>
    GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have ha : (fun j : Fin e => ((fun _ : Fin e => fsH ι) j).a) = fun _ : Fin e => fun _ : K => (1 : ℤ) := by
    funext j k
    simp [fsH, HermLine.ofMetrics]
  obtain ⟨hq, hd⟩ := ZCombLimit.genericFibre hP
  have hpos := hPos ℚ K ι _ e hq hd
  rw [GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e _ 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at hpos
  rw [hDeg K ι P e (fun _ => fsH ι) 2 hP hS Nat.prime_two, ha,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  exact_mod_cast hpos

end GroundTheory.Heights₂.Heights.HilbertSamuel
