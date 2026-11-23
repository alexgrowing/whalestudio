import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Proposition5OfThreeParts
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.GramExponentArithmetic
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeOfOneLeMul
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembFinal
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.TestSideWords

theorem proposition5_holds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60 :=
  proposition5_of_three_parts D CLa Ck Crk Cdeg (restPick D CLa Ck Crk Cdeg) (restMemb D CLa Ck Crk Cdeg) (restNum D CLa Ck Crk Cdeg)

theorem stmtE_of_mem (D : Formalism.BasicNotions.D7) (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_MP D hM fun CLa Ck Crk Cdeg => proposition5_holds D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
