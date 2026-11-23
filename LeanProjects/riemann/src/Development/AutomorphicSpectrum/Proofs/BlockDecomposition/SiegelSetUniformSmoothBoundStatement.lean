import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_uniform_smooth_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (b : Fin m → ℝ → GAd σ J) (Ω₀ : Set (GAd σ J)) (C δ₁ : ℝ), (∀ i, IsRealLine σ J (b i)) ∧ IsCompact Ω₀ ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g u : GAd σ J) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseInf σ J u δ → ∀ c : Fin m → ℝ, (∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ c i) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.Mean.mean_value | exact GlobalTheory.CompanionTheory.RapidDecay.Mean.mean_value | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.Mean.mean_value <;> assumption)
