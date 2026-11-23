import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinUnfoldingRapidDecay
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_unfolding_rapid_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d d₁ : ℕ}
    (W : Spc F E d) (H' : Plane E d d₁) (μ : Measure (UA σ W.J)), μ.IsHaarMeasure →
    ∀ (𝓕 : Set (UA σ W.J)) (f : UA σ W.J → ℂ) (Ez : ℂ → UA σ W.J → UA σ W.J → ℂ) (s₀ : ℂ) (R₀ : ℝ), Continuous f →
      (∀ N : ℕ, IntegrableOn (fun h => ‖f h‖ * (qht h : ℝ) ^ N) 𝓕 μ) →
      (∀ h, ∃ C : ℝ, ∀ u ∈ unip σ W H', (qht (u * h) : ℝ) ≤ C) →
      GlobalTheory.CuspDbl.IsRegFam (fun h : UA σ W.J => (qht h : ℝ)) s₀ Ez →
      (∀ s : ℂ, R₀ < s.re → IsCT H' (fun h => ∫ h' in 𝓕, f h' * Ez s h h' ∂μ) 0) →
      IsCT H' (fun h => ∫ h' in 𝓕, f h' * Ez s₀ h h' ∂μ) 0 := by
  first | exact @GlobalTheory.CuspCont.isCT_integral_of_regFam | exact GlobalTheory.CuspCont.isCT_integral_of_regFam | (intros; apply GlobalTheory.CuspCont.isCT_integral_of_regFam <;> assumption)
