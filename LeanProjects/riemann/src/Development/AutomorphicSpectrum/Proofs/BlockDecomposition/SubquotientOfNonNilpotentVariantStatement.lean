import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_of_non_nilpotent_variant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], SubOfNonNil' F ι := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSub.subOfNonNil_of_subquot | exact GlobalTheory.CompanionTheory.HeckeSub.subOfNonNil_of_subquot | (intros; apply GlobalTheory.CompanionTheory.HeckeSub.subOfNonNil_of_subquot <;> assumption)
