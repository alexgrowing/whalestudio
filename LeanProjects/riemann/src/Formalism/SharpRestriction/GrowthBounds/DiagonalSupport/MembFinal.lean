import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembershipOfThreeParts
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembVB
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembXXb

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

theorem restMemb (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMemb D CLa Ck Crk Cdeg :=
  membership_of_three_parts restValBdG restXXG_b restDdG_holds D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
