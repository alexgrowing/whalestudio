import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_generation : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  first | exact @GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | exact GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | (intros; apply GlobalTheory.CompanionTheory.EisMir.mirGen_of_core <;> assumption)
