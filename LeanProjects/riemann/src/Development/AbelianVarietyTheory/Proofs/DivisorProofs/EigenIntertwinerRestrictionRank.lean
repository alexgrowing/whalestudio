import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousFunctionalLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneIntertwinesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKExpand

theorem thetaSum_eq_mixed : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ Ψ ∈ schA F (Fin n × Fin d),
      Summable (fun ξ : Fin n → E => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ))) ∧
      thetaSum F Ψ = C₀ * ∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW
  obtain ⟨c, hc⟩ := GlobalTheory.T.additive_homogeneous_functional_linear hKP F E σ B n d X W M hB hM hXW
    (fun Ψ => ∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ)))
    (GlobalTheory.T.evaluation_map_adapted_plane_injective hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW).1
    (GlobalTheory.T.evaluation_map_adapted_plane_injective hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW).2
    (GlobalTheory.T.evaluation_map_adapted_plane_surjective hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW)
    (GlobalTheory.T.evaluation_map_adapted_plane_continuous hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW)
  obtain ⟨Ψ₀, hΨ₀, hne⟩ := GlobalTheory.T.evaluation_map_adapted_plane_intertwines hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hc Ψ₀ hΨ₀)
  refine ⟨c⁻¹, inv_ne_zero hc0, fun Ψ hΨ => ⟨GlobalTheory.T.evaluation_map_adapted_plane_equivariant hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW Ψ hΨ, ?_⟩⟩
  have := hc Ψ hΨ
  beta_reduce at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.ThKExpand
