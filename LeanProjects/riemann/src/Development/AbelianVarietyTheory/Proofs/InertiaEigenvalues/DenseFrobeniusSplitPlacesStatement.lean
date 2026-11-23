import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_frobenius_split_places : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), Dense {σ : GE N | ∃ w, SplitOut N i w ∧ ∃ B : ValuationSubring N.Om, Formalism.ConjugateSelfDual.IsPlaceOver (F := H.E) B w ∧ Formalism.ConjugateSelfDual.IsFrob (F := H.E) B (Formalism.ConjugateSelfDual.normV w) σ} := by
  first | exact @GlobalTheory.FrobDense.dense_frob | exact GlobalTheory.FrobDense.dense_frob | (intros; apply GlobalTheory.FrobDense.dense_frob <;> assumption)
