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

namespace GlobalTheory.ThK.ConeEuler

theorem continuous_idemUnit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ε : AF F) (hε : ε * ε = ε) : Continuous (idemUnit E ε hε) := by
  rw [Units.continuous_iff]
  constructor
  · exact ((continuous_const_smul ε).comp Units.continuous_val).add continuous_const
  · exact ((continuous_const_smul ε).comp Units.continuous_coe_inv).add continuous_const

theorem continuous_unitAt_unitArch :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
      (∀ v : Pl F, Continuous (unitAt E v)) ∧ Continuous (unitArch F E) := by
  intro F E _ _ _ _ _
  exact ⟨fun v => continuous_idemUnit _ _, continuous_idemUnit _ _⟩

end GlobalTheory.ThK.ConeEuler
