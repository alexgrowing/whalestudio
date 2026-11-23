import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TheoremMOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeHerm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepro
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrame
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UuInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSymBeta
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRankOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem thmM_of_xi (h : UnitaryGroupStructuralFacts) (hXi : Formalism.FourierDecayAlt.B.XiExists) : ThmM :=
  theoremM_of h hXi (stBeHerm h) (stBePos h) (stSchurW h) (stSInt h) stSchurG (stPairs h) (stBeConv h) (stBeEquiv h)
    (stRepro h) (stSmooth h) stFrame (stInvGroup h) stInvChar stInvCC (stReps h) (stTransM h) (stSym h) (stSymBeta h)
    (stBetaInf h) (stDichoG h) (stDichoW h) (stMixed h) rankOneMinors

theorem thmM : ThmM := thmM_of_xi multiplicity_one_hypotheses_hold ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end ReciprocityTheory.ChartRestriction.DS.Mult1
