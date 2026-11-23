import Formalism.SharpRestriction.GrowthBounds.BinomialRatio
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SegFormZeroRight
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Beyond44OfRestRawTail
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OPlusAtOf
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyMinorDvd
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PsiRes0Ne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFFinal

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem witt_identification_of_admitted {D : Formalism.BasicNotions.D7} (hA : admitted D) : WittIdent :=
  hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem restForm (D : Formalism.BasicNotions.D7) : RestForm :=
  restForm_of_oplus (Formalism.MainNotions.G.GLWeightTheory.lemma_five_two_first_holds D) restOPlus

theorem stmtEExt_of_rawTail1 {D : Formalism.BasicNotions.D7} (h : admitted D → RestRawTail1) : ExtendedClosedForm D :=
  stmtEExt_of fun hA => paired_lifts_of_identity (witt_identification_of_admitted hA) (h hA) (restForm D)

def RawTailReduction : Prop := RestAsmRT

theorem stmtEExt_of_15c {D : Formalism.BasicNotions.D7} (h : admitted D → RawTailReduction) : ExtendedClosedForm D :=
  stmtEExt_of_rawTail1 fun hA => restRawTail1_of (third_key_of_order key3Ord) (local_fourth_of_order (loc4Ord_of (loc4Div_of loc4Res))) (h hA)

theorem stmtE_of_15c {D : Formalism.BasicNotions.D7} (h : admitted D → RawTailReduction) : ClosedFormOfAdmitted D := (stmtEExt_of_15c h).closed_of_extended_closed

end Formalism.MainNotions.ColumnSystems.Pf
