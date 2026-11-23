import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormArchLeSupInfinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_arch_le_sup_infinite : ∀ (F : Type) [Field F] [NumberField F] (a : AF F),
    (∀ w, ‖archAt F w a‖ ≤ ‖evI F a‖) ∧ ∀ B : ℝ, 0 ≤ B → (∀ w, ‖archAt F w a‖ ≤ B) → ‖evI F a‖ ≤ B := by
  first | exact @GlobalTheory.ThetaDecay.norm_evI_sup | exact GlobalTheory.ThetaDecay.norm_evI_sup | (intros; apply GlobalTheory.ThetaDecay.norm_evI_sup <;> assumption)
