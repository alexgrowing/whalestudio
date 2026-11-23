import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairSeesawIdentityStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKMixX

theorem mixed_model_plane_X : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      (∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e) ∧
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ h t g₁ m, IsLevi H t g₁ m → ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (u * m, h) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, h) (e Φ) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  refine ⟨GlobalTheory.T.adapted_plane_pair_restriction hKP F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁, ?_⟩
  intro e he h t g₁ m hm u hu Φ hΦ
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    fun x Φ hΦ => hP.weil.isUSplitting.pres x Φ hΦ
  have hsplit : ((u * m, h) : UA σ X.J × UA σ W.J) = ((u, 1) * (m, 1)) * (1, h) := by simp
  rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    GlobalTheory.T.adapted_plane_pair_theta_integral hKP F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu _ (pres _ _ (pres _ _ hΦ)),
    GlobalTheory.T.adapted_plane_pair_seesaw_identity hKP F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t g₁ m hm _ (pres _ _ hΦ),
    GlobalTheory.T.adapted_plane_pair_local_factor hKP F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he h Φ hΦ,
    ← Module.End.mul_apply, ← map_mul]
  simp

end GlobalTheory.ThKMixX
