import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
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
theorem _root_.GlobalTheory.T.ideles_compact_of_local_bounds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (Pl F)) (A : Set (AE F E)ˣ) (B : Pl F → Set (AE F E)ˣ), IsCompact A → (∀ v ∈ S, IsCompact (B v)) →
    IsCompact {l : (AE F E)ˣ | unitArch F E l ∈ A ∧ (∀ v ∈ S, unitAt E v l ∈ B v) ∧ ∀ v ∉ S, unitAt E v l ∈ unitsAt E v} := by
  first | exact @GlobalTheory.IdeleCyl.isCompact_cyl | exact GlobalTheory.IdeleCyl.isCompact_cyl | (intros; apply GlobalTheory.IdeleCyl.isCompact_cyl <;> assumption)
