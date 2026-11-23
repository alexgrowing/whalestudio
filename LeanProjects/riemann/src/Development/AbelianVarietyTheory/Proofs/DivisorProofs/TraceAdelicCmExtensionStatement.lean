import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_adelic_cm_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : AF F, Algebra.trace (AF F) (AE F E) (algebraMap (AF F) (AE F E) x) = 2 * x) ∧ ∀ c : AE F E, algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) c) = c + cA σ c := by
  first | exact @GlobalTheory.CMTrace.adele_trace | exact GlobalTheory.CMTrace.adele_trace | (intros; apply GlobalTheory.CMTrace.adele_trace <;> assumption)
