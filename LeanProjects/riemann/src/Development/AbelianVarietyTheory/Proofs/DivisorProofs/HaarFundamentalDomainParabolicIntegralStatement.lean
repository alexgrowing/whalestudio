import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainParabolicIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_fundamental_domain_parabolic_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ (μX : Measure (UA σ X.J)) (μ₁ : Measure (UA σ X₁.J)) (D₁ : Set (UA σ X₁.J)), μX.IsHaarMeasure → μ₁.IsHaarMeasure → IsFundamentalDomain (ratU σ X₁.J) D₁ μ₁ → ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab (X := X) B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ Q : Subgroup (UA σ X.J), (∀ q, q ∈ Q ↔ q ∈ ratU σ X.J ∧ mat q *ᵥ incV F H.x = incV F H.x) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ 𝓓 : Set (UA σ X.J), IsFundamentalDomain Q 𝓓 μX → ∀ f : UA σ X.J → ℝ≥0∞, AEMeasurable f μX → (∀ q ∈ Q, ∀ g, f (q * g) = f g) → (∀ u ∈ unip σ X H, ∀ g, f (u * g) = f g) → ∫⁻ g in 𝓓, f g ∂μX ≤ C * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in D₁, f (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μ₁ ∂μ ∂μK := by
  first | exact @GlobalTheory.FoldLine.lintegral_fd_le_iwasawa | exact GlobalTheory.FoldLine.lintegral_fd_le_iwasawa | (intros; apply GlobalTheory.FoldLine.lintegral_fd_le_iwasawa <;> assumption)
