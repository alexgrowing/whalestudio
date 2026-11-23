import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMap
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_part_diagonal_map : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  first | exact @GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | exact GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | (intros; apply GlobalTheory.CompanionTheory.CptDiag.cptPart_diag <;> assumption)
