import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsEqEmbedding
import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_eq_embedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), g ∈ ratPts σ J → ∃ η : GRat σ J, g = ratEmb σ J η := by
  first | exact @GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts | exact GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts | (intros; apply GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts <;> assumption)
