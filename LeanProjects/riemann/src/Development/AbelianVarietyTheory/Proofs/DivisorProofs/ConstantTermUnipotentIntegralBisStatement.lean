import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralBis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_unipotent_integral_bis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} (H : Plane E n n₁) (f c : UA σ Y.J → ℂ), IsCT H f c →
    (∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) →
    (∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1) →
    ∀ (h₁ : UA σ Y₁.J) (r : UA σ Y.J), IsLevi (W₁ := Y₁) H 1 h₁ r → r ∈ ratU σ Y.J → ∀ x, c (r * x) = c x := by
  first | exact @GlobalTheory.CTLevi.ct_levi | exact GlobalTheory.CTLevi.ct_levi | (intros; apply GlobalTheory.CTLevi.ct_levi <;> assumption)
