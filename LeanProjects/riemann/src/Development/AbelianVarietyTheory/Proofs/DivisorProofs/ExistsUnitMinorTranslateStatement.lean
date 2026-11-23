import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_minor_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y.rank = n →
    ∃ E : GL (Fin n) k, E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet <;> assumption)
