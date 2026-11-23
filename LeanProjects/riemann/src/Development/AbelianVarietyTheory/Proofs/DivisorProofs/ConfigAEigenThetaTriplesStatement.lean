import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenThetaTriples
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_eigen_theta_triples : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ γ : {x : Fin (b + 2) → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J,
      (∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x) →
    ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ Φ ∈ PolData B G.M, ∀ h,
      ∫ g in G.M.dom, ∑' x, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))) ∂G.M.μ = ∫ g in 𝓓, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ))) ∂G.M.μ := by
  first | exact @GlobalTheory.ThK.Unfold.integral_tsum_isotropic_eq | exact GlobalTheory.ThK.Unfold.integral_tsum_isotropic_eq | (intros; apply GlobalTheory.ThK.Unfold.integral_tsum_isotropic_eq <;> assumption)
