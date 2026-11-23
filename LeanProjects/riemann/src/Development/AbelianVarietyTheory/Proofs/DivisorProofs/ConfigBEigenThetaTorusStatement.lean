import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenThetaTorus
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_eigen_theta_torus : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ ∈ PolData B G.M, ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → ∀ h, G₁.M.I om₁ (e (om (1, m * h) Φ)) 1 = (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * G₁.M.I om₁ (e (om (1, h) Φ)) h₁ := by
  first | exact @GlobalTheory.ThK.evalZero_levi | exact GlobalTheory.ThK.evalZero_levi | (intros; apply GlobalTheory.ThK.evalZero_levi <;> assumption)
