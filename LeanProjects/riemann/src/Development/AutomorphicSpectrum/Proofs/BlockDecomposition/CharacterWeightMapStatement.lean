import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterWeightMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_weight_map : ChWMap := by
  first | exact @GlobalTheory.CompanionTheory.CharInf.chWMap | exact GlobalTheory.CompanionTheory.CharInf.chWMap | (intros; apply GlobalTheory.CompanionTheory.CharInf.chWMap <;> assumption)
