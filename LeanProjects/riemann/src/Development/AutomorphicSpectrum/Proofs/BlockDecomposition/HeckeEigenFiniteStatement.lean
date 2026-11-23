import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFinite
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigen_finite : PositivityTheory.Rg.BcB.F.Tail.PExp.HkEFin := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | exact GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | (intros; apply GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin <;> assumption)
