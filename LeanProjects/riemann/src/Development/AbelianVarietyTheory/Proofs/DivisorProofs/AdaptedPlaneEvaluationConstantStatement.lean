import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_evaluation_constant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ e₀, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∃ C₀ : ℂ, C₀ ≠ 0 ∧
      ((∀ x, form σ X.J x x = 0 → x = 0) → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g,
        IsCT H' (theta om Φ g) fun h => C₀ * thetaSum F (e₀ (om (g, h) Φ))) ∧
      ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
        ∀ e, IsEv B M M₂ H.ι H'.ι (isoA H H') e → ∃ C₁ : ℂ, C₁ ≠ 0 ∧
        ∀ γ : {x : Fin n → E // x ≠ 0 ∧ form σ X.J x x = 0} → UA σ X.J,
          (∀ x, γ x ∈ ratU σ X.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x) →
          ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g,
            (∀ h, Summable fun x => thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ)))) ∧
            IsCT H' (theta om Φ g) fun h => C₀ * thetaSum F (e₀ (om (g, h) Φ)) +
              C₁ * ∑' x, thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))) := by
  first | exact @GlobalTheory.ThKConstTerm.constantTerm_theta | exact GlobalTheory.ThKConstTerm.constantTerm_theta | (intros; apply GlobalTheory.ThKConstTerm.constantTerm_theta <;> assumption)
