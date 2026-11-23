import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttached
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hkFrob_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → HkFrob i s := by
  first | exact @GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt | exact GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt | (intros; apply GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt <;> assumption)
