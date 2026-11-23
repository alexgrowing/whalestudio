import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAExistsNonzeroCoefficient
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_exists_nonzero_coefficient : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M', ∀ g, IsCT H' (theta om' Φ' g) (fun h => C₀ * thetaSum F (e' (om' (g, h) Φ'))) := by
  first | exact @GlobalTheory.ThK.ctSmallZeroTheta | exact GlobalTheory.ThK.ctSmallZeroTheta | (intros; apply GlobalTheory.ThK.ctSmallZeroTheta <;> assumption)
