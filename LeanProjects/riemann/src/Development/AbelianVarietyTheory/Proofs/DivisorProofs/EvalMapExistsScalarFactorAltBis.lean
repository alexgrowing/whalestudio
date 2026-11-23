import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapExistsScalarFactorAltAlt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_thetaSum_rho_vecMulVec_mul_pow_bounded : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ N K : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ ξ : Fin n → E, (∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ))‖ *
        (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C := by
  first | exact @GlobalTheory.XiTermDecay.decay | exact GlobalTheory.XiTermDecay.decay | (intros; apply GlobalTheory.XiTermDecay.decay <;> assumption)
