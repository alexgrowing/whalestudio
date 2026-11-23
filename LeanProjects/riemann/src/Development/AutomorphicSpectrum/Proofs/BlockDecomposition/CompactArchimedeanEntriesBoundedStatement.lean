import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactArchimedeanEntriesBounded
import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_archimedean_entries_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C → ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact | exact GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact <;> assumption)
