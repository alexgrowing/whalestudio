import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegelSmall
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSTop

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem model_existence_of_siegel (hG : SiegelSmall) : ModelEx := model_existence_of_siegel_small hG (smallS_of' chartFacts sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
