import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSet
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_unit_minor_set : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    IsClopen (GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d) := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet <;> assumption)
