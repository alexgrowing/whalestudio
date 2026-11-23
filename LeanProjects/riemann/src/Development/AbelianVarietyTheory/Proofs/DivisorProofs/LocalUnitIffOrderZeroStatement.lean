import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitIffOrderZero
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
theorem _root_.GlobalTheory.T.local_unit_iff_order_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (l : idelesAt E (evFin F v)), (l.1 ∈ unitsAt E v ↔ ordV v l = 0) := by
  first | exact @GlobalTheory.TateUnits.mem_unitsAt_iff_ordV_eq_zero | exact GlobalTheory.TateUnits.mem_unitsAt_iff_ordV_eq_zero | (intros; apply GlobalTheory.TateUnits.mem_unitsAt_iff_ordV_eq_zero <;> assumption)
