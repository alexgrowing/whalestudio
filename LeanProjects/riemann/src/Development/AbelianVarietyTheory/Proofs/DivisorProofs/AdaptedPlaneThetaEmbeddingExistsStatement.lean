import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneThetaEmbeddingExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_theta_embedding_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∃ (N : ℕ) (emb : (Fin N → ℝ) → (Fin n → AE F E)) (lam : (Fin n → E) → Fin N → ℝ), Function.Injective lam ∧
      ∀ (ξ : Fin n → E) (t : Fin N → ℝ),
        B.ψ ((M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))).1 ⬝ᵥ (M.co.e (Matrix.vecMulVec (emb t) (incV F H'.x))).2 -
          (M.co.e (Matrix.vecMulVec (emb t) (incV F H'.x))).1 ⬝ᵥ (M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))).2) =
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)) := by
  first | exact @GlobalTheory.RealFreq.injective_real_frequencies | exact GlobalTheory.RealFreq.injective_real_frequencies | (intros; apply GlobalTheory.RealFreq.injective_real_frequencies <;> assumption)
