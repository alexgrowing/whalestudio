import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealMemIffOrder
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open GlobalTheory.TateUnr

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ideal_mem_iff_order : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 → ∀ l : idelesAt E (evFin F v),
    (compFin F E v (l.1 : AE F E) ∈ locId v 𝔞 ↔ ∀ w : aboveF (L := E) F v, FractionalIdeal.count E w.1 𝔞 ≤ ordV v l w) := by
  first | exact @GlobalTheory.TateUnr.mem_locId_iff_count_le_ordV | exact GlobalTheory.TateUnr.mem_locId_iff_count_le_ordV | (intros; apply GlobalTheory.TateUnr.mem_locId_iff_count_le_ordV <;> assumption)
