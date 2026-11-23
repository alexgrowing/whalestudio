import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedSphericalZetaIntegralOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_spherical_zeta_integral_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (s : ℂ), IsUnram ν →
    kInd k n ∈ SB (Matrix (Fin n) (Fin n) k) ∧ gjZ ν s (kInd k n) = 1 := by
  first | exact @GlobalTheory.GJReg.kInd_mem_SB_and_gjZ_eq_one | exact GlobalTheory.GJReg.kInd_mem_SB_and_gjZ_eq_one | (intros; apply GlobalTheory.GJReg.kInd_mem_SB_and_gjZ_eq_one <;> assumption)
