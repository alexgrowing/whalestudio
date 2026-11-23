import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpen
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_cone_isOpen : ∀ n : ℕ, IsOpen (PositivityTheory.RgBcC.cone n) := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone | exact GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone <;> assumption)
