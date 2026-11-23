import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerComponentAtPlaceMem
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
theorem _root_.GlobalTheory.T.stabilizer_component_at_place_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} {X : Spc F E n} (K : Subgroup (UA σ X.J)), IsStab B K → ∀ k ∈ K, ∀ v : Pl F, compAt σ X.J v k ∈ K := by
  first | exact @GlobalTheory.ThK.ConeEuler.StabCompAt.compAt_mem_of_isStab | exact GlobalTheory.ThK.ConeEuler.StabCompAt.compAt_mem_of_isStab | (intros; apply GlobalTheory.ThK.ConeEuler.StabCompAt.compAt_mem_of_isStab <;> assumption)
