import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMovesYByIotaAndXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationPairRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermAdaptedEvaluationReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseInverseFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseRationalValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseNontrivialCharacterStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoNonzero

set_option maxHeartbeats 400000 in

theorem integral_isotropic_nonzero_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ w : Fin d₁ → E, w ≠ 0 →
      ∫ u in 𝓕, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ))))) ∂μ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hP μ 𝓕 hμ
    h𝓕 h1 Ψ hΨ w hw
  have hlaw : ∀ u ∈ unip σ W H', thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w))
      (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ))))) =
      B.ψ (GlobalTheory.IsoPhase.phase σ W H' w u) * thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w))
        (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)))) := by
    intro u hu
    obtain ⟨z, β, hz⟩ := GlobalTheory.T.unipotent_moves_y_by_iota_and_x F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hP.base.cm hP.skew hH' u⁻¹ (inv_mem hu)
    rw [GlobalTheory.T.adapted_evaluation_pair_relation hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ hH u hu z β hz
      Ψ hΨ, GlobalTheory.T.herm_adapted_evaluation_reduction F E σ B n d₁ X W₁ M₁ r s n₁ X₁ H j₀ j₁ M₂ hP.base hP.herm hH e' he' _ ?_ w z,
      GlobalTheory.T.isotropic_phase_inverse_formula F E σ B d d₁ W W₁ H' i₀ i₁ hH' u w z β hz]
    exact he₀.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std _ Ψ hΨ)
  haveI := hμ
  obtain ⟨g, hg, hψg⟩ := GlobalTheory.T.isotropic_phase_nontrivial_character F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hP.base hP.skew hH' w hw
  have hadd := GlobalTheory.T.isotropic_phase_additive F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hP.base.cm hP.skew hH' w
  refine GlobalTheory.IsoPhase.setIntegral_eq_zero_of_mul_right σ W H' μ 𝓕 h𝓕 h1 (fun u : unip σ W H' => thetaSum F (e'
      (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w))
        (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ)))))) ?_ ⟨g, hg⟩
    (B.ψ (GlobalTheory.IsoPhase.phase σ W H' w g)) hψg ?_
  · intro γ hγ x
    have hγU : (γ : UA σ W.J) ∈ ratU σ W.J := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨c, hc⟩ := GlobalTheory.T.isotropic_phase_rational_value F E σ d d₁ W H' w γ.1 hγU
    simp only [Subgroup.coe_mul]
    rw [hlaw _ (mul_mem γ.2 x.2), hlaw _ x.2, hadd _ γ.2 _ x.2, AddChar.map_add_eq_mul, hc, hP.base.std.2.1 c, one_mul]
  · intro x
    simp only [Subgroup.coe_mul]
    rw [hlaw _ (mul_mem x.2 hg), hlaw _ x.2, hadd _ x.2 _ hg, AddChar.map_add_eq_mul]
    ring

end GlobalTheory.IsoNonzero
