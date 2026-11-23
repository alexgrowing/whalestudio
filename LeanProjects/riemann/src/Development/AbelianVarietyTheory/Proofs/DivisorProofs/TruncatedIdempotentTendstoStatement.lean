import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedIdempotentTendsto
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_idempotent_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : AE F E),
    (∀ u : AF F, At (evI F) u → u • c = 0) →
    Tendsto (fun T : Finset (Pl F) => GlobalTheory.TruncFix.idem T • c) atTop (𝓝 c) := by
  first | exact @GlobalTheory.TruncFix.tendsto_idem_smul | exact GlobalTheory.TruncFix.tendsto_idem_smul | (intros; apply GlobalTheory.TruncFix.tendsto_idem_smul <;> assumption)
