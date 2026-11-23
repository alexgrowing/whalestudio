import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElement
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_local_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
  ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := by
  first | exact @GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL | exact GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL | (intros; apply GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL <;> assumption)
