import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAConstantTermThetaLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_constant_term_theta_lift : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ X om om', IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M', ∀ c : UA σ G.V'.J → UA σ G.W.J → ℂ, (∀ g, IsCT H' (theta om' Φ' g) (c g)) → IsCT H' (G.M'.I om' Φ') (fun h => ∫ g in G.M'.dom, c g h ∂G.M'.μ) := by
  first | exact @GlobalTheory.ThKFubQZero.ctFubini | exact GlobalTheory.ThKFubQZero.ctFubini | (intros; apply GlobalTheory.ThKFubQZero.ctFubini <;> assumption)
