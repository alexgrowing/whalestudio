import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleRestrictedProductStructure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_restricted_product_structure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    GlobalTheory.RestrMeas.IsRestrGroup (X := (AE F E)ˣ) (W := Unit) (V := Pl F)
      (fun _ => (unitArch F E).codRestrict (idelesAt E (evI F)) unitArch_mem)
      (fun v => (unitAt E v).codRestrict (idelesAt E (evFin F v)) (unitAt_mem v))
      (fun v => (unitsAt E v).subgroupOf (idelesAt E (evFin F v))) := by
  first | exact @GlobalTheory.IdeleRestr.isRestrGroup_ideles | exact GlobalTheory.IdeleRestr.isRestrGroup_ideles | (intros; apply GlobalTheory.IdeleRestr.isRestrGroup_ideles <;> assumption)
