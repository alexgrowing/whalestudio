import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneSecondForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_adapted_plane_second_form : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ vf : unip σ X H → (Fin d₂ → AE F E), (∀ u, ∃ a : AE F E, mat u.1⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ vf u + a • incV F H.x) →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ u' ∈ unip σ W H',
      ∫ u in 𝓕, thetaSum F (M₁.co.rho B.ψ (Matrix.vecMulVec (vf u) (incV F H'.x)) (e (om (1, u') Φ))) ∂μ =
        ∫ u in 𝓕, thetaSum F (M₁.co.rho B.ψ (Matrix.vecMulVec (vf u) (incV F H'.x)) (e Φ)) ∂μ := by
  first | exact @GlobalTheory.NwAvgInv.avg_invariant | exact GlobalTheory.NwAvgInv.avg_invariant | (intros; apply GlobalTheory.NwAvgInv.avg_invariant <;> assumption)
