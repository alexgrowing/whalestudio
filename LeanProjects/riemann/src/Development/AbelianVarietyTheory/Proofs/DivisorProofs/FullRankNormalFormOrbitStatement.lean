import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_normal_form_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n ≤ d →
    ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  first | exact @GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | exact GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | (intros; apply GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq <;> assumption)
