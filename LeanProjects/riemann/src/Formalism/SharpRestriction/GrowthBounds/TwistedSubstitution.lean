import Formalism.SharpRestriction.GrowthBounds.DualFockLinear
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Proposition5Gram
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.OperatorWeightBoundHolds
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemRed
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aMonomial
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aGeneratorProducts
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.SymGSupport
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg

noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.TestSideCounting

theorem stmtE_of_TenMP (hT : TenOp) (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenNS hT D fun CLa Ck Crk Cdeg => restNS_of D CLa Ck Crk Cdeg 26 2 24 60 (hM _ _ _ _) (hP _ _ _ _)

theorem stmtE_of_MP (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenMP tensor_operators_holds D hM hP

end Formalism.MainNotions.TestSideWords
