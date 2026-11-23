import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterNormalizedEquivariantFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_normalized_equivariant_functional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → IsUnram ν →
    ∃ l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ, IsEqv ν z l ∧ l ((intM k (Fin n) (Fin n)).indicator 1) = 1 := by
  first | exact @GlobalTheory.GJReg.exists_regGJ | exact GlobalTheory.GJReg.exists_regGJ | (intros; apply GlobalTheory.GJReg.exists_regGJ <;> assumption)
