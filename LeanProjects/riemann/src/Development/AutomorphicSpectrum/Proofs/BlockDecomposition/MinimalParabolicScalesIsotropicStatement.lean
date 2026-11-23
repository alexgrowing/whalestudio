import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicScalesIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_scales_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar <;> assumption)
