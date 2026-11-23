import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBExistsNonzeroCoefficient
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_exists_nonzero_coefficient : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ ∈ PolData B G.M, ∃ (c : UA σ G.V.J → UA σ G.W.J → ℂ) (A₁ : UA σ G.W.J → ℂ), (∀ g, IsCT H' (theta om Φ g) (c g)) ∧ HasLaw G₁.W H' X.α (((b + 2 : ℕ) : ℝ) / 2) A₁ ∧ ∀ h, IntegrableOn (fun g => c g h - C₀ * thetaSum F (e (om (g, h) Φ))) G.M.dom G.M.μ ∧ ∫ g in G.M.dom, (c g h - C₀ * thetaSum F (e (om (g, h) Φ))) ∂G.M.μ = A₁ h := by
  first | exact @GlobalTheory.ThK.ConeV.coneV | exact GlobalTheory.ThK.ConeV.coneV | (intros; apply GlobalTheory.ThK.ConeV.coneV <;> assumption)
