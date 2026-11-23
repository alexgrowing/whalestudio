import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ContinuousFinId
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSplit

namespace PositivityTheory.KCo

theorem kCoinv_of_dict (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hD : DictSt) : GlobalTheory.ThK.KCoinv :=
  kCoinv_of surjectivity_statement (irrSt_of hB) hD nu_statement so_statement good_split_of_cm

end PositivityTheory.KCo
