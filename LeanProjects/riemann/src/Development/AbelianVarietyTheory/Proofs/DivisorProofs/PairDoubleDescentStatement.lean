import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_double_descent : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (M₁ : Model σ X₁ W₁),
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ e, IsEv B M M₁ H.ι H'.ι (isoA H H') e → ∀ f : Fn F n d →ₗ[ℂ] Fn F n₁ d₁,
    (∀ (z : Matrix (Fin n₁) (Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d),
      f (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (f Φ)) →
    (∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin n × Fin d), f (M.co.rho B.ψ u Φ) = f Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), f Φ = c • e Φ := by
  first | exact @GlobalTheory.ThK.EvLawUniq.eq_smul_isEv | exact GlobalTheory.ThK.EvLawUniq.eq_smul_isEv | (intros; apply GlobalTheory.ThK.EvLawUniq.eq_smul_isEv <;> assumption)
