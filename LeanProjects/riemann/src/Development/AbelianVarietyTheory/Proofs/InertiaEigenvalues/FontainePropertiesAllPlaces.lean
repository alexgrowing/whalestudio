import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissible

theorem fontaineProperties_all_places : ∀ D : D7, Formalism.MainNotions.PairedCharacterCondition.FontaineAtPlacesOverL (D := D) := by
  intro D l _ K LL
  exact GlobalTheory.FontaineAll.fontaineAt_all D l K LL

end GlobalTheory.FontaineAdmissible
