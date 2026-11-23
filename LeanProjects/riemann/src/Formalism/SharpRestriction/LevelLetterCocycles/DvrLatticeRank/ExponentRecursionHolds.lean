import Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionOfDimension

noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem exponent_recursion_holds : ExpansionFormHypothesis := fun D HW F Cm _ _ _ hA hd hr =>
  CrystallineExponents.exponent_recursion_of_dimension D HW F Cm hA.1 hA.2.2.2.2.2.2.2.2.2.2.1 fun l _ K LL hG T hT c τ =>
    ((hr l K LL hG T hT c).trans (hd l K LL ⟨1, hG⟩ T hT τ).symm).le

end Formalism.MainNotions.N.Ln34

end
