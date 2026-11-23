import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ), letI : MeasurableSpace (P.adicCompletion L) := borel _; ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)), ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  first | exact @GlobalTheory.HaarMat.exists_haar_intMat | exact GlobalTheory.HaarMat.exists_haar_intMat | (intros; apply GlobalTheory.HaarMat.exists_haar_intMat <;> assumption)
