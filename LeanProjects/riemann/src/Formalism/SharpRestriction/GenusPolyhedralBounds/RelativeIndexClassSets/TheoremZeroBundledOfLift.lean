import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthBaseT0
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthPoleInLift
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLengths

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem lenBase_all {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} :
    ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j), LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  fun _ _ _ _ _ => length_base_t0

theorem lenPoleL_all {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} :
    ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j), LenPoleL (X := X) (ka := ka) (wL := wL) (wF := wF) := by
  intro j X ka wL wF G la Q S CRm T e c hOk hLift hW
  exact length_pole_t0 G la Q S CRm T e c hOk hW hLift

theorem theorem_zero_of_named_inputs {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} : Conclusion1OfComb (D := D) (B := B) (P := P) :=
  theorem_zero_split_of_lengths lenBase_all lenPoleL_all

theorem theorem_zero_bundled_of_lift {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} (hL : LiftAll D B P) :
    Conclusion1Of2 (D := D) (B := B) (P := P) :=
  theorem_zero_bundled_of_split hL theorem_zero_of_named_inputs

end Formalism.MainNotions.Gaps.EtaleWeightGaps
