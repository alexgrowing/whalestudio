import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetSmoothModerateGrowth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_smooth_moderate_growth : GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (c₀ : E), c₀ ≠ 0 → IsHermND σ (c₀ • J.map σ) →
    ∀ (φ : UA σ J → ℂ) (φ' : GAd σ (c₀ • J.map σ) → ℂ), (∀ (g : UA σ J) (g' : GAd σ (c₀ • J.map σ)), g.1 = g'.1 → φ' g' = φ g) →
    GlobalTheory.SiegelSet.IsSmoothModerate σ (c₀ • J.map σ) φ' → GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • J.map σ) φ' →
    ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖φ h‖ * (qht h : ℝ) ^ N ≤ C := by
  first | exact @GlobalTheory.SiegelSet.rapidDecay_qht | exact GlobalTheory.SiegelSet.rapidDecay_qht | (intros; apply GlobalTheory.SiegelSet.rapidDecay_qht <;> assumption)
