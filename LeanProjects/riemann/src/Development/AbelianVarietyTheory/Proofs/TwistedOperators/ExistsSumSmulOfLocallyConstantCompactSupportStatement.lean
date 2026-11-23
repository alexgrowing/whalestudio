import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumSmulOfLocallyConstantCompactSupport
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport : ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V] [Module ℂ V] (T : Z → V) (_ : IsLocallyConstant T) (K : Set Z) (_ : IsCompact K) (_ : ∀ y, y ∉ K → T y = 0), ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  first | exact @GlobalTheory.LocConstTensor.exists_sum | exact GlobalTheory.LocConstTensor.exists_sum | (intros; apply GlobalTheory.LocConstTensor.exists_sum <;> assumption)
