import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_group_of_unit_minor_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d →
    E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet <;> assumption)
