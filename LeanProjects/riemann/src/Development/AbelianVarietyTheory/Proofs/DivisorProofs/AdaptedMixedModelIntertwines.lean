import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEvaluationStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKExpandXLin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n₁ d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem rho_add (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) (Φ Ψ : Fn F n d) :
    M.co.rho ψ u (Φ + Ψ) = M.co.rho ψ u Φ + M.co.rho ψ u Ψ := by
  funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

theorem rho_smul (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ) (Φ : Fn F n d) :
    M.co.rho ψ u (c • Φ) = c • M.co.rho ψ u Φ := by
  funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring

theorem lin_of_summable {ι : Type} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d) (he : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n₁ × Fin d))
    (u : ι → Matrix (Fin n) (Fin d) (AE F E))
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), Summable fun ξ => thetaSum F (e (M.co.rho ψ (u ξ) Ψ))) :
    (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ Ψ' ∈ schA F (Fin n × Fin d),
      (∑' ξ, thetaSum F (e (M.co.rho ψ (u ξ) (Ψ + Ψ')))) =
        (∑' ξ, thetaSum F (e (M.co.rho ψ (u ξ) Ψ))) + ∑' ξ, thetaSum F (e (M.co.rho ψ (u ξ) Ψ'))) ∧
    ∀ c : ℂ, ∀ Ψ : Fn F n d,
      (∑' ξ, thetaSum F (e (M.co.rho ψ (u ξ) (c • Ψ)))) = c * ∑' ξ, thetaSum F (e (M.co.rho ψ (u ξ) Ψ)) := by
  refine ⟨fun Ψ hΨ Ψ' hΨ' => ?_, fun c Ψ => ?_⟩
  · have h : ∀ ξ, thetaSum F (e (M.co.rho ψ (u ξ) (Ψ + Ψ'))) =
        thetaSum F (e (M.co.rho ψ (u ξ) Ψ)) + thetaSum F (e (M.co.rho ψ (u ξ) Ψ')) := fun ξ => by
      rw [rho_add, map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ hΨ))
        (he _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Ψ' hΨ'))
    rw [tsum_congr h]
    exact (hs Ψ hΨ).tsum_add (hs Ψ' hΨ')
  · have h : ∀ ξ, thetaSum F (e (M.co.rho ψ (u ξ) (c • Ψ))) = c * thetaSum F (e (M.co.rho ψ (u ξ) Ψ)) := fun ξ => by
      rw [rho_smul, map_smul]
      exact GlobalTheory.WeilM.thetaSum_smul F c _
    rw [tsum_congr h, tsum_mul_left]

theorem main_of_summ (hsumm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ φ ∈ schA F (Fin n × Fin d₁), Summable (fun w : Fin d₁ → E => thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)))) :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    (∀ φ ∈ schA F (Fin n × Fin d₁), ∀ φ' ∈ schA F (Fin n × Fin d₁), (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ + φ')))) = (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ)))) + (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ'))))) ∧
      ∀ c : ℂ, ∀ φ ∈ schA F (Fin n × Fin d₁), (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (c • φ)))) = c * (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ)))) := by
  intro hK F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he hB hXW
  obtain ⟨h1, h2⟩ := lin_of_summable M₁ B.ψ hB.std e' he.maps _
    (hsumm hK F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he hB hXW)
  exact ⟨h1, fun c Ψ _ => h2 c Ψ⟩

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    (∀ φ ∈ schA F (Fin n × Fin d₁), ∀ φ' ∈ schA F (Fin n × Fin d₁), (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ + φ')))) = (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ)))) + (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ'))))) ∧
      ∀ c : ℂ, ∀ φ ∈ schA F (Fin n × Fin d₁), (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (c • φ)))) = c * (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ)))) :=
  main_of_summ GlobalTheory.T.adapted_mixed_model_evaluation

end GlobalTheory.ThKExpandXLin
