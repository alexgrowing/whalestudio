import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCharpolySeparableOfElliptic
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_charpoly_separable_of_elliptic : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
  (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  first | exact @GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | exact GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | (intros; apply GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl <;> assumption)
