import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairExtensionEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairLocalFactorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixWTorus

theorem evalZero_torus : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ t m, IsLevi (W₁ := W₁) H' t 1 m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (1, m) Φ) = ((χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) • e Φ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m hm Φ hΦ
  by_cases h0 : ∃ Ψ ∈ schA F (Fin n × Fin d), e Ψ ≠ 0
  · obtain ⟨hmaps, hheis, hinv, hadm⟩ := GlobalTheory.T.skew_adapted_pair_extension_eigen F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m hm
    obtain ⟨k, hk⟩ := GlobalTheory.T.skew_adapted_pair_theta_integral hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he _ hmaps hheis hinv hadm
    have hk' : ∀ Ψ ∈ schA F (Fin n × Fin d), e (om (1, m) Ψ) = k • e Ψ := fun Ψ hΨ => hk Ψ hΨ
    rw [← GlobalTheory.T.skew_adapted_pair_local_factor hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he t m hm k hk' h0]
    exact hk' Φ hΦ
  · push_neg at h0
    have h1 : om (1, m) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres (1, m) Φ hΦ
    rw [h0 _ h1, h0 _ hΦ, smul_zero]

end GlobalTheory.MixWTorus
