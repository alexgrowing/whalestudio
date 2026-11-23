import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAll
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_element_integral_almost_all : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | exact GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually <;> assumption)
