import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesAboveAndNontrivialAbs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_above_and_nontrivial_abs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ w : HeightOneSpectrum (𝓞 E), ∃ x : (w.adicCompletion E)ˣ, absE F E (locIdele F w x) ≠ 1 := by
  first | exact @GlobalTheory.PlaceAbove.places | exact GlobalTheory.PlaceAbove.places | (intros; apply GlobalTheory.PlaceAbove.places <;> assumption)
