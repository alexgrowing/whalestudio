import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower

open Formalism.GaloisCohomology

namespace UpperTheory.V.Win

theorem thmBab_of_lemmaK (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hFW : Published.FerreroWashington) (hK : ∃ CK : ℝ, LemmaK CK) : ∃ K : BConst, ∀ Ct : ℝ, 1 ≤ Ct → ThmBab K Ct :=
  have hA : Two.TowerBound := fun l _ L _ _ R h => PropA.aBound_of_isTower hP hF hT l L R h
  thmBab_of hK (Two.fixedIn hFW hA) (Two.twoIn hFW hA)

end UpperTheory.V.Win
