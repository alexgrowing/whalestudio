import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicPairEisensteinExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_pair_eisenstein_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ), IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → 1 ≤ n → 1 ≤ d →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∃ (Ez : ℂ → UA σ W.J → UA σ W.J → ℂ) (φ : ℂ → UA σ W.J → ℂ) (s₀ κ : ℂ) (R₀ : ℝ), κ ≠ 0 ∧
      (∀ h h', GlobalTheory.ThKLiftCusp.kern M om Φ₁ Φ₂ h h' = κ * Ez s₀ h h') ∧
      GlobalTheory.CuspDbl.IsRegFam (fun h : UA σ W.J => (qht h : ℝ)) s₀ Ez ∧
      ∀ s : ℂ, R₀ < s.re → Integrable (φ s) μ ∧
        ∀ 𝓕 : Set (UA σ W.J), IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
        ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) →
        (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → GlobalTheory.ThKLiftCusp.IsCuspW W f →
        ∀ h, ∫ h' in 𝓕, f h' * Ez s h h' ∂μ = ∫ g, φ s g * f (h * g) ∂μ := by
  first | exact @GlobalTheory.CuspDbl.anisoFamily | exact GlobalTheory.CuspDbl.anisoFamily | (intros; apply GlobalTheory.CuspDbl.anisoFamily <;> assumption)
