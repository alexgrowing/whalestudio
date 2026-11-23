import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitaryWittExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_witt_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_hE <;> assumption)
