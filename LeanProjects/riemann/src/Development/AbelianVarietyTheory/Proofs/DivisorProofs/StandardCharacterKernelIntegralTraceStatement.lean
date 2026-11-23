import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterKernelIntegralTrace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_character_kernel_integral_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (t : AF F) (a : F) (ht : evI F t = 0)
    (hv : ∀ v, evFin F v t = algebraMap F (Fv F v) a) (h1 : ψ t = 1), ∃ z : ℤ, Algebra.trace ℚ F a = z := by
  first | exact @GlobalTheory.DenomTrace.trace_int_of_psi_eq_one | exact GlobalTheory.DenomTrace.trace_int_of_psi_eq_one | (intros; apply GlobalTheory.DenomTrace.trace_int_of_psi_eq_one <;> assumption)
