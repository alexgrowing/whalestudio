import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetIdelesInIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped nonZeroDivisors TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_ideles_in_ideal : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 →
    MeasurableSet {l : (AE F E)ˣ | ∀ v : Pl F, compFin F E v (l : AE F E) ∈ GlobalTheory.LocIdeal.locId v 𝔞} := by
  first | exact @GlobalTheory.LocIdealMeas.measurableSet_locId | exact GlobalTheory.LocIdealMeas.measurableSet_locId | (intros; apply GlobalTheory.LocIdealMeas.measurableSet_locId <;> assumption)
