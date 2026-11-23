import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, IsCharAF F ψ := by
  first | exact @GlobalTheory.GaugeEx.CharZero.exists_isCharAF | exact GlobalTheory.GaugeEx.CharZero.exists_isCharAF | (intros; apply GlobalTheory.GaugeEx.CharZero.exists_isCharAF <;> assumption)
