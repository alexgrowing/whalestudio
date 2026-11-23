import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.Separate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftsSeparateOfSeparatingData

section
namespace UpperTheory.Lit
open GlobalTheory.SepRows
theorem bessel_separate_of_step_gap (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hT : RowTower) :
    SizeGap → GoodRows → RowConv → WeakSep → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  Bur.separate_of_burGapPos burGapPos GlobalTheory.T.dualCoefSpace_isTensorOverRealPlaces (_root_.GlobalTheory.T.theta_lifts_separate_points P) hT
end UpperTheory.Lit
end
