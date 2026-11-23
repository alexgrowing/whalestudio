import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_ex : SecEx := by
  first | exact @GlobalTheory.CompanionTheory.SecThrough.secEx | exact GlobalTheory.CompanionTheory.SecThrough.secEx | (intros; apply GlobalTheory.CompanionTheory.SecThrough.secEx <;> assumption)
