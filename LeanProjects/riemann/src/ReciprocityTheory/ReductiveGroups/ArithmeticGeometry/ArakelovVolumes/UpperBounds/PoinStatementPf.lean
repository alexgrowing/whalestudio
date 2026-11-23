import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem poin_of_inputs (hLU : LUStatement (E := E)) (hS : PoinPf.SumBallStatement (E := E))
    (hF : PoinPf.FFStatement (E := E)) : PoinStatement (E := E) :=
  PoinPf.poin_of (PoinPf.loc_of (PoinPf.subMeanLoc_of hLU) hS)
    (PoinPf.ball_of PoinPf.subMean_holds hS) hF

theorem poin_holds : PoinStatement (E := E) :=
  poin_of_inputs lu_holds PoinPf.sumBall_holds PoinPf.ff_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
