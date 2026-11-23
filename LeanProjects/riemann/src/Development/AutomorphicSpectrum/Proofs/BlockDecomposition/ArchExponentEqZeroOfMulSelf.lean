import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

theorem archExponent_eq_zero_of_mul_self {K : Type _} [Field K] [NumberField K]
    (w : InfinitePlace K) {μ : HeckeCharacter K} (hμ : μ * μ = 1) : archExponent w μ = 0 := by
  have h : archExponent w μ = -archExponent w μ := by
    rw [← archExponent_inv, ← eq_inv_of_mul_eq_one_left hμ]
  linarith

end GlobalTheory.CompanionTheory.EisRk1
