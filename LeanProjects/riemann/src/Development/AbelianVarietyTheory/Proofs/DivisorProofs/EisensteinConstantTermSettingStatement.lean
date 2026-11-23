import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermSetting
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_constant_term_setting : GlobalTheory.Published.EisensteinIsotropicLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c → ∃ mid : ℂ → GAd σ J → ℂ, (∀ g, DifferentiableOn ℂ (mid · g) {s : ℂ | ((n : ℝ) - 1) / 2 - 1 < s.re}) ∧ (∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 →
      ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g, ∫ u in 𝓕, Eis s (u.1 * g) ∂μ =
        (h g : ℂ) ^ (s + (((n : ℂ) - 1) / 2)) + mid s g + c s * (h g : ℂ) ^ (-s + (((n : ℂ) - 1) / 2))) := by
  first | exact @GlobalTheory.EisCT.constTerm | exact GlobalTheory.EisCT.constTerm | (intros; apply GlobalTheory.EisCT.constTerm <;> assumption)
