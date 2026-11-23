import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMovesYByIotaAndXStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationPairRelationStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.IsoDecomp

theorem decomp_ev : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ u ∈ unip σ W H',
    ∃ (y : Fin d₁ → AE F E) (b : AE F E), incM F H'.ι *ᵥ y = mat u⁻¹ *ᵥ incV F H'.y - incV F H'.y - b • incV F H'.x ∧
      ∀ Ψ ∈ schA F (Fin n × Fin d), e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ)) =
        M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) y) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ hH χX χW om r s r' s' hP u hu
  obtain ⟨z, β, hz⟩ := GlobalTheory.T.unipotent_moves_y_by_iota_and_x F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hP.base.cm hP.skew hH' u⁻¹ (inv_mem hu)
  refine ⟨z, β, by rw [hz]; abel, fun Ψ hΨ => ?_⟩
  exact GlobalTheory.T.adapted_evaluation_pair_relation hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ hH
    u hu z β hz Ψ hΨ

end GlobalTheory.ThK.IsoDecomp
