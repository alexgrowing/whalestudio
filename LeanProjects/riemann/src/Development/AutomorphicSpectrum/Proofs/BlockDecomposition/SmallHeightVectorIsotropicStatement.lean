import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_height_vector_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt | exact GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt | (intros; apply GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt <;> assumption)
