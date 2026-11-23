import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_inverse_reduction : PositivityTheory.SphericalProduct.InvStepU := by
  first | exact @GlobalTheory.CompanionTheory.InvStep.invStepU | exact GlobalTheory.CompanionTheory.InvStep.invStepU | (intros; apply GlobalTheory.CompanionTheory.InvStep.invStepU <;> assumption)
