import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvertibleExistsNonzeroMinor
import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_invertible_exists_nonzero_minor : ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
    L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse | exact GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse | (intros; apply GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse <;> assumption)
