import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhere
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_sign_almost_everywhere : KapOrbAE := by
  first | exact @GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | (intros; apply GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE <;> assumption)
