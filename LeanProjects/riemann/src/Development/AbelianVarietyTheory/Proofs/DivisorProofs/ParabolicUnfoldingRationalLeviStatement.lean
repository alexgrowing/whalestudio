import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicUnfoldingRationalLevi
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_unfolding_rational_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (f : UA σ Y.J → ℂ),
    (∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) → ∀ (γ : UA σ Y₁.J) (m₀ : UA σ Y.J), m₀ ∈ ratU σ Y.J →
    IsLevi (W₁ := Y₁) H 1 γ m₀ → ∀ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ x, ∫ u in 𝓕, f (u.1 * (m₀ * x)) ∂μ = ∫ u in 𝓕, f (u.1 * x) ∂μ := by
  first | exact @GlobalTheory.UnipCTLevi.constantTerm_levi | exact GlobalTheory.UnipCTLevi.constantTerm_levi | (intros; apply GlobalTheory.UnipCTLevi.constantTerm_levi <;> assumption)
