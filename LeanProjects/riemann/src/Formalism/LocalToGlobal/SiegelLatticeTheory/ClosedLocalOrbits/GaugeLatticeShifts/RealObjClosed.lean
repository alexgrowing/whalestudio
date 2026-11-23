import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FlagExtensionRegularity
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst

open Formalism.BasicNotions Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf

theorem realObj_inNuX {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ) : InNuX X u u' sc := by
  have hC : 0 ≤ DisintegrationConstant X u u' sc := by
    unfold DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hO : ∀ c, 0 ≤ hilbertSchmidtSqGram X u u' sc c := fun c => by
    unfold hilbertSchmidtSqGram hs2
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : Measurable (fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (InfCut.wt_cont X u u').measurable)
  unfold InNuX intOOe intCe nuM
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine MeasureTheory.lintegral_congr fun c => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul' (hO c), ← ENNReal.ofReal_mul hC, mul_assoc]

end Formalism.L2.SG.Pf
