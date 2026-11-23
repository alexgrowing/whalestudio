import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc

namespace PositivityTheory.KCo

theorem so_coinvariants_of_bernstein (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  soCoinv_of hB dictionary_statement hK

end PositivityTheory.KCo
