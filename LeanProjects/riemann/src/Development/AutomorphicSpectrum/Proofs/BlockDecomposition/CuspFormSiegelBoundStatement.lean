import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormSiegelBound
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_siegel_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J, height σ J g ≤ C * height σ J (γ * g) ^ A := by
  first | exact @GlobalTheory.CompanionTheory.SiegelHt.height_le_pow | exact GlobalTheory.CompanionTheory.SiegelHt.height_le_pow | (intros; apply GlobalTheory.CompanionTheory.SiegelHt.height_le_pow <;> assumption)
