import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_vector_measure_isAddHaar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ), (nuInf E k).IsAddHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | exact GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | (intros; apply GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure <;> assumption)
