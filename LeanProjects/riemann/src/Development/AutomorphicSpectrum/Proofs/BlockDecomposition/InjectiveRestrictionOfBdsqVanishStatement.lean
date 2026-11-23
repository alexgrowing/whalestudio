import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveRestrictionOfBdsqVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_restriction_of_bdsq_vanish : PositivityTheory.RgBcC.RealD.BdSqL → PositivityTheory.RgBcC.RealD.VanKL → PositivityTheory.RgBcC.RealD.InjRL := by
  first | exact @GlobalTheory.CompanionTheory.InjRL.injRL_of | exact GlobalTheory.CompanionTheory.InjRL.injRL_of | (intros; apply GlobalTheory.CompanionTheory.InjRL.injRL_of <;> assumption)
