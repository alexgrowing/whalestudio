import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_subquotients : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  first | exact @GlobalTheory.CompanionTheory.RepFinSubq.finSubq | exact GlobalTheory.CompanionTheory.RepFinSubq.finSubq | (intros; apply GlobalTheory.CompanionTheory.RepFinSubq.finSubq <;> assumption)
