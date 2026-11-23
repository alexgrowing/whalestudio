import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDense
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i), FrobDual i s → CharDual i s := by
  first | exact @GlobalTheory.CharDualDense.charDual_of_frobDual | exact GlobalTheory.CharDualDense.charDual_of_frobDual | (intros; apply GlobalTheory.CharDualDense.charDual_of_frobDual <;> assumption)
