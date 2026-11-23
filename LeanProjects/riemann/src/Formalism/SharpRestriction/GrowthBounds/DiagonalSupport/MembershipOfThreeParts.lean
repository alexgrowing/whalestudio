import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecIdentity
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ProjectionMemPartialSpan
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ImportsAlt
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembAlgF
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDegF
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembLabF

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

theorem decomposition_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) : RestDecG :=
  restDecG_of atl valSlice valComp hVB hXX hDd

theorem membership_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestMemb D CLa Ck Crk Cdeg :=
  membership_of_four_parts (decomposition_of_three_parts hVB hXX hDd) restAlgG restDegG restLabG D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
