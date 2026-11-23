import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.SmoothDesignExistence.PlaceDegreeData

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

structure FamS (𝒞 : FamClass) (C0 : ℝ) (ca : List ℝ → AdmissibleBoundsFromSource.AdmC) : Prop where
  caOk : ∀ {eps : ℝ} (Fm : FamP eps), (ca Fm.cOut).Ok (Fm.CYL + 1)
  resid : Closed 𝒞 fun Fm _ => S.ResidEv Fm
  rowsTie : Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X, PlaceDegreeData.RowsTie (Fm.D x i) X

  p76 : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.PeriodFamilyStatement Fm (S.gcOf Fm C0) (ca Fm.cOut)
  familyClosedAdmissibleFirst : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF1 Fm (S.gcOf Fm C0)
  familyClosedAdmissibleSecond : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF2 Fm (S.gcOf Fm C0)
  familyClosedAdmissibleThird : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF3 Fm (S.gcOf Fm C0)
  familyClosedAdmissibleFourth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF4 Fm (S.gcOf Fm C0)
  familyClosedAdmissibleFifth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF5 Fm (S.gcOf Fm C0)
  familyClosedAdmissibleSixth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF6 Fm (S.gcOf Fm C0) (ca Fm.cOut).A5 (ca Fm.cOut).cL
  familyClosedAdmissibleSeventh : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF7 Fm (S.gcOf Fm C0) (ca Fm.cOut).cN (ca Fm.cOut).CN
  familyClosedAdmissibleEighth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF8 Fm (S.gcOf Fm C0) (ca Fm.cOut).CE
  familyClosedAdmissibleNinth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.admF9 Fm (S.gcOf Fm C0) (ca Fm.cOut).CA (ca Fm.cOut).CA' (ca Fm.cOut).Ce
  familyClosedAdmissibleEleventh : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.FamilyWeylAndVandermonde Fm (S.gcOf Fm C0) (ca Fm.cOut).ep0 (ca Fm.cOut).CV
  familyClosedAdmissibleThirteenth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.FamilyThirteenthHypothesis Fm (S.gcOf Fm C0) (ca Fm.cOut).C1 (ca Fm.cOut).C2 (ca Fm.cOut).c5
    (ca Fm.cOut).CA
  familyClosedAdmissibleFourteenth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.FamilyFourteenthHypothesis Fm (S.gcOf Fm C0)
  familyClosedAdmissibleFifteenth : Closed 𝒞 fun Fm _ => AdmissibleBoundsFromSource.FamilyFifteenthHypothesis Fm (S.gcOf Fm C0)

end Formalism.MainNotions.Pk

end
