import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAbsPowerLocallyConstant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_abs_power_locally_constant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E), Continuous ν →
    ∀ (z : ℕ) (v : Pl F), IsLocallyConstant (fun l : idelesAt E (evFin F v) => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) := by
  first | exact @GlobalTheory.LocConstChar.isLocallyConstant_char_absPow | exact GlobalTheory.LocConstChar.isLocallyConstant_char_absPow | (intros; apply GlobalTheory.LocConstChar.isLocallyConstant_char_absPow <;> assumption)
