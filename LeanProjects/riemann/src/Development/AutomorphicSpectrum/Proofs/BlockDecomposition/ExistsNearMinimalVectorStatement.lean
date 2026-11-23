import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNearMinimalVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_near_minimal_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_nearMin | exact GlobalTheory.CompanionTheory.RedCov.exists_nearMin | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_nearMin <;> assumption)
