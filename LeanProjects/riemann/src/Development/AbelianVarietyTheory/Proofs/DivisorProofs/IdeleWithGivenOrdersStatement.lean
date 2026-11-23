import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleWithGivenOrders
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
theorem _root_.GlobalTheory.T.idele_with_given_orders : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (k : aboveF (L := E) F v → ℤ), ∃ l : idelesAt E (evFin F v), ordV v l = k := by
  first | exact @GlobalTheory.TateUnr.ordV_surjective | exact GlobalTheory.TateUnr.ordV_surjective | (intros; apply GlobalTheory.TateUnr.ordV_surjective <;> assumption)
