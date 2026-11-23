import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationIntertwinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationCharacterTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationRepresentationStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measUA
local instance borelUA' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

namespace GlobalTheory.ThKSwap

theorem swap_of_bound {ι G : Type*} [Countable ι] [MeasurableSpace G] (μ : Measure G) (s : Set G) (hs : μ s ≠ ⊤)
    (f : ι → G → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) (μ.restrict s)) (C : ℝ)
    (hb : ∀ u, Summable (fun i => ‖f i u‖) ∧ ∑' i, ‖f i u‖ ≤ C) :
    Summable (fun i => ∫ u in s, f i u ∂μ) ∧ ∫ u in s, (∑' i, f i u) ∂μ = ∑' i, ∫ u in s, f i u ∂μ := by
  have hfin : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hlin : ∑' i, ∫⁻ u in s, ‖f i u‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (fun i => (hm i).enorm)]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in s, ENNReal.ofReal C ∂μ) ?_ (lintegral_mono fun u => ?_)
    · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · simp_rw [← ofReal_norm_eq_enorm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb u).1]
      exact ENNReal.ofReal_le_ofReal (hb u).2
  refine ⟨?_, integral_tsum hm hlin⟩
  refine Summable.of_norm_bounded (g := fun i => (∫⁻ u in s, ‖f i u‖ₑ ∂μ).toReal) (ENNReal.summable_toReal hlin) fun i => ?_
  refine (norm_integral_le_lintegral_norm _).trans_eq ?_
  simp_rw [ofReal_norm_eq_enorm]

theorem countable_of_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem bound_lem : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Ψ ∈ schA F (Fin n × Fin d),
      ∃ C : ℝ, ∀ u : unip σ W H', Summable (fun ξ : Fin n → E => ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ)))‖) ∧
        ∑' ξ : Fin n → E, ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ)))‖ ≤ C := by
  intro hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hG e₀ he χX χW om r s r' s' hP Ψ hΨ
  obtain ⟨K, hKc, hcov⟩ := GlobalTheory.T.adapted_plane_evaluation_character_twist hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hG e₀ he χX χW om r s r' s' hP
  obtain ⟨C, hC⟩ := GlobalTheory.T.adapted_plane_evaluation_representation hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hG e₀ he χX χW om r s r' s' hP Ψ hΨ K hKc
  refine ⟨C, fun u => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov u
  have key : ∀ ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) = thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, (γ⁻¹ * u).1) Ψ))) := fun ξ => by
    have := GlobalTheory.T.adapted_plane_evaluation_equivariant hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hG e₀ he χX χW om r s r' s' hP Ψ hΨ ξ γ (γ⁻¹ * u) hγ
    rwa [mul_inv_cancel_left] at this
  simp_rw [key]
  exact hC _ hk

theorem swap : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin n × Fin d),
      Summable (fun ξ : Fin n → E => ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) ∂μ) ∧
      ∫ u in 𝓕, (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ)))) ∂μ = ∑' ξ : Fin n → E, ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) ∂μ := by
  intro hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hG e₀ he χX χW om r s r' s' hP μ 𝓕 _ _ h1 Ψ hΨ
  obtain ⟨C, hC⟩ := bound_lem hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hG e₀ he χX χW om r s r' s' hP Ψ hΨ
  haveI := countable_of_numberField E
  exact swap_of_bound μ 𝓕 (by simp [h1]) _
    (fun ξ => (GlobalTheory.T.adapted_plane_evaluation_intertwines hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hG e₀ he χX χW om r s r' s' hP Ψ hΨ ξ).aestronglyMeasurable) C hC

end GlobalTheory.ThKSwap
