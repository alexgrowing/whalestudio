import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfL

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem measInv_holds : MeasInvStatement (E := E) := by
  intro r X x0 x0' h0 h0' φ hφm hφ
  exact MI.lintegral_cpt_muX_indep_of_isOrtho X h0 h0' hφm hφ

end ReciprocityTheory.ChartRestriction.G.AR.Up
