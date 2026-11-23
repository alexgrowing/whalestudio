import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_compFin_mem_intLoc_adele (z : AE F E) :
    ∀ᶠ v : Pl F in cofinite, compFin F E v z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz => filter_upwards [hy, hz] with v h h' using by rw [map_add]; exact add_mem h h'
  | tmul a e =>
    filter_upwards [a.2.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := evFin F v a) h (1 : 𝓞 E)) h'
    change evFin F v a ⊗ₜ[F] e ∈ _
    simpa using this

omit [NumberField E] in

theorem compFin_unitAt_self (v : Pl F) (l : (AE F E)ˣ) :
    compFin F E v (unitAt E v l : AE F E) = compFin F E v l := by
  change compFin F E v (eFin v • (l : AE F E) + (1 - eFin v) • 1) = _
  have h : evFin F v (eFin v) = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  rw [map_add, compFin_smul, compFin_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]

theorem eventually_unitAt_mem_unitsAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (l : (AE F E)ˣ) : ∀ᶠ v in cofinite, unitAt E v l ∈ unitsAt E v := by
  filter_upwards [eventually_compFin_mem_intLoc_adele (l : AE F E),
    eventually_compFin_mem_intLoc_adele ((l⁻¹ : (AE F E)ˣ) : AE F E)] with v h h'
  refine mem_unitsAt.2 ⟨unitAt_mem v l, ?_, ?_⟩
  · rwa [compFin_unitAt_self]
  · rwa [← map_inv, compFin_unitAt_self]

end GlobalTheory.ThK.ConeEuler

end
