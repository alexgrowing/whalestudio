import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_ideles_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsOpen {l : (AE F E)ˣ | ∀ v : Pl F, unitAt E v l ∈ unitsAt E v} := by
  first | exact @GlobalTheory.ThK.ConeEuler.isOpen_setOf_forall_unitAt_mem_unitsAt | exact GlobalTheory.ThK.ConeEuler.isOpen_setOf_forall_unitAt_mem_unitsAt | (intros; apply GlobalTheory.ThK.ConeEuler.isOpen_setOf_forall_unitAt_mem_unitsAt <;> assumption)
