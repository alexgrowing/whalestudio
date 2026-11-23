import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyStandardLocalHaarMeasures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_standardLocalHaarMeasures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Nonempty (StdMeas b) := by
  first | exact @GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | exact GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | (intros; apply GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas <;> assumption)
