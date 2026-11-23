import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorBoundByHeight
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
theorem _root_.GlobalTheory.T.denominator_bound_by_height : ∀ (F : Type) [Field F] [NumberField F] (y : F), ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
    IsIntegral ℤ ((m : F) * y) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | exact GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.Den.denominator_le <;> assumption)
