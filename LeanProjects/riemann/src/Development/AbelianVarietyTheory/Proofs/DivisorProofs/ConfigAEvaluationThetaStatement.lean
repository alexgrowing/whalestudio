import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationTheta
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_evaluation_theta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (k : UA σ G.V.J) (a : AE F E), mat k *ᵥ incV F H.x = a • incV F H.x →
    (∀ z : Fin b → AE F E, ∃ c : AE F E, mat k *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + c • incV F H.x) →
    ∃ c : ℂ, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e (om (k, 1) Ψ) = c • e Ψ := by
  first | exact @GlobalTheory.ThKNScalar.twist_scalar | exact GlobalTheory.ThKNScalar.twist_scalar | (intros; apply GlobalTheory.ThKNScalar.twist_scalar <;> assumption)
