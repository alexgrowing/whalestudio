import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardResidueRingCompletionChosenUniformiser
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueRing_completion_chosenUniformiser : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  first | exact @GlobalTheory.ResidueCardUnif.card_kF_piP | exact GlobalTheory.ResidueCardUnif.card_kF_piP | (intros; apply GlobalTheory.ResidueCardUnif.card_kF_piP <;> assumption)
