import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairDual
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_adapted_plane_pair_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ h₁ m, IsLevi H' 1 h₁ m →
        (∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) Φ ∈ schA F (Fin n × Fin d₁)) ∧
        (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
          M₁.co.rho B.ψ z ((om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) Φ)) ∧
        (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) (M.co.rho B.ψ u Φ) =
          (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) Φ) := by
  first | exact @GlobalTheory.EvTwist.conj_ev | exact GlobalTheory.EvTwist.conj_ev | (intros; apply GlobalTheory.EvTwist.conj_ev <;> assumption)
