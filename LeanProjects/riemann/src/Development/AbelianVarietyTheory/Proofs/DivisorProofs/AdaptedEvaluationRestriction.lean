import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousFunctionalLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSkewComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelIntertwinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelVanishingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKExpandX

theorem thetaSum_eq_mixedX : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ φ ∈ schA F (Fin n × Fin d₁),
      Summable (fun w : Fin d₁ → E => thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ))) ∧
      thetaSum F φ = C * ∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ hev n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev' hB hXW
  obtain ⟨r, s, r', s', hX, hW⟩ := hXW
  have hW₁ := GlobalTheory.ThK.KernelZero.isSkew_complement F E σ B hB d d₁ W W₁ H' i₀ i₁ r' s' hW hH'
  have hXW₁ : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s' := ⟨r, s, r' - 1, s' - 1, hX, hW₁⟩
  have hl := GlobalTheory.T.adapted_mixed_model_intertwines hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev' hB hXW₁
  obtain ⟨c, hc⟩ := GlobalTheory.T.additive_homogeneous_functional_linear hKP F E σ B n d₁ X W₁ M₁ hB hM₁ hXW₁
    (fun φ => (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ))))) hl.1 hl.2
    (GlobalTheory.T.adapted_mixed_model_support hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev' hB hXW₁)
    (GlobalTheory.T.adapted_mixed_model_equivariance hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev' hB hXW₁)
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.T.adapted_mixed_model_vanishing hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev' hB hXW₁
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hc φ₀ hφ₀)
  refine ⟨c⁻¹, inv_ne_zero hc0, fun φ hφ => ⟨GlobalTheory.T.adapted_mixed_model_evaluation hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev' hB hXW₁ φ hφ, ?_⟩⟩
  have := hc φ hφ
  beta_reduce at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.ThKExpandX
