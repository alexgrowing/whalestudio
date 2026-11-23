import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivCoreUpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem localUnfoldBStatement_holds : LocalUnfoldBStatement (E := E) :=
  LUB.localUnfoldB_of lu_holds

theorem ontoWeightStatement_holds : OntoWeightStatement (E := E) :=
  OW.ontoWeight_of localUnfoldBStatement_holds

theorem divCoreStatement_holds : DivCoreStatement (E := E) :=
  divCore_up_of ontoWeightStatement_holds upDiv_holds DivStartStatement_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
