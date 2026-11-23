import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions : ∀ (F : Type) [Field F] [NumberField F], Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  first | exact @GlobalTheory.GaugeEx.nice_ainf_fv | exact GlobalTheory.GaugeEx.nice_ainf_fv | (intros; apply GlobalTheory.GaugeEx.nice_ainf_fv <;> assumption)
