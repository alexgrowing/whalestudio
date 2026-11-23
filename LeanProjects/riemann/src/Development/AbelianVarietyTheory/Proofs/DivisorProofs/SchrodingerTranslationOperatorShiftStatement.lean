import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerTranslationOperatorShift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_translation_operator_shift : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (a b : κ → mixedEmbedding.mixedSpace F),
    ∃ t : ℂ, ∀ f g g' : SInf F κ, ⇑g = schrF (trP F κ) w ⇑f → ⇑g' = schrF (trP F κ) w ⇑(dOp a b f) →
      g' = dOp a b g + t • g := by
  first | exact @GlobalTheory.ThK.EvAt0.PolD.schrF_dOp_conj | exact GlobalTheory.ThK.EvAt0.PolD.schrF_dOp_conj | (intros; apply GlobalTheory.ThK.EvAt0.PolD.schrF_dOp_conj <;> assumption)
