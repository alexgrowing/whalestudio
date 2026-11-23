import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_identity_assembly : EpMain → DGood → Master → SideOf → Term → ZetaK → SideUnfold → SideConv → ZetaOne → Core := by
  first | exact @GlobalTheory.CompanionTheory.EisCore.wall_core | exact GlobalTheory.CompanionTheory.EisCore.wall_core | (intros; apply GlobalTheory.CompanionTheory.EisCore.wall_core <;> assumption)
