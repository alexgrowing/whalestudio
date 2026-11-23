import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAtInfinityAdeleWithComplexCompone
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : AE F E, At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  first | exact @GlobalTheory.RealLift.exists_atInf_piInf_eq | exact GlobalTheory.RealLift.exists_atInf_piInf_eq | (intros; apply GlobalTheory.RealLift.exists_atInf_piInf_eq <;> assumption)
