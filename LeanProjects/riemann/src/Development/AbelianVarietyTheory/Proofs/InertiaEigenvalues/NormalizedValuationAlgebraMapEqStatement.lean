import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationAlgebraMapEq
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuation_algebraMap_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (l : ℕ) (x : O), Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  first | exact @GlobalTheory.nval_algebraMap_eq | exact GlobalTheory.nval_algebraMap_eq | (intros; apply GlobalTheory.nval_algebraMap_eq <;> assumption)
