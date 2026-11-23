import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairHypPlaneAdaptedLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_hyp_plane_adapted_lift : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∃ C₀ : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J,
      ∃ (T : UA σ W.J → ℂ) (γ : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0} → UA σ W.J),
        Continuous T ∧ (∀ u ∈ unip σ W H', ∀ h, T (u * h) = T h) ∧
        (∀ p ∈ ratU σ W.J, mat p *ᵥ incV F H'.x = incV F H'.x → ∀ h, T (p * h) = T h) ∧
        (∀ w, γ w ∈ ratU σ W.J ∧ mat (γ w) *ᵥ incV F w.1 = incV F H'.x) ∧
        (∀ h, Summable fun w => ‖T (γ w * h)‖) ∧ (∃ (C : ℝ) (k : ℕ), ∀ h, ∑' w, ‖T (γ w * h)‖ ≤ C * (qht h : ℝ) ^ k) ∧
        ∀ (μN : Measure (unip σ X H)) (𝓕N : Set (unip σ X H)), μN.IsHaarMeasure →
          IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕N μN → μN 𝓕N = 1 →
          ∀ h, ∫ u in 𝓕N, theta om Φ (u.1 * g) h ∂μN = C₀ * thetaSum F (e (om (g, h) Φ)) + ∑' w, T (γ w * h) := by
  first | exact @GlobalTheory.KernelTower.constantTerm_kernel | exact GlobalTheory.KernelTower.constantTerm_kernel | (intros; apply GlobalTheory.KernelTower.constantTerm_kernel <;> assumption)
