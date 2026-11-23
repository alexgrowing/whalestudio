import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleCompatibility
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_triple_compatibility : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)) (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → G.p = 0 →
    ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∀ Φ ∈ PolData B G.M, G.M.I om Φ = 0 → G₁.M.I om₁ (e Φ) = 0 := by
  first | exact @GlobalTheory.ThK.stepB_anisotropic | exact GlobalTheory.ThK.stepB_anisotropic | (intros; apply GlobalTheory.ThK.stepB_anisotropic <;> assumption)
