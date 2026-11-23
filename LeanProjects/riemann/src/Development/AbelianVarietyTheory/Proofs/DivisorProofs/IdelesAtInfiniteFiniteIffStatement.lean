import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesAtInfiniteFiniteIff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped nonZeroDivisors TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideles_at_infinite_finite_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : (AE F E)ˣ),
    (l ∈ idelesAt E (evI F) ↔ ((GlobalTheory.IdeleLogHom.toE F E l : AdeleRing (𝓞 E) E)).2 = 1) ∧
    (l ∈ idelesAt E (fun x : AF F => x.2) ↔ ((GlobalTheory.IdeleLogHom.toE F E l : AdeleRing (𝓞 E) E)).1 = 1) := by
  first | exact @GlobalTheory.IdeleTensorParts.mem_idelesAt_iff | exact GlobalTheory.IdeleTensorParts.mem_idelesAt_iff | (intros; apply GlobalTheory.IdeleTensorParts.mem_idelesAt_iff <;> assumption)
