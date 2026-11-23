import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.FirstSubSecondLeviFamily
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionActionHolds

namespace PositivityTheory.RgBcC.RealD

theorem multFor_of (hP : InvPick) (hLS : LevStab) (hLR : LevRel) (hSC : SemiCls) (hCC : CapCls) (h4 : LeviCommutantWordReduction)
    (h5 : CapelliProductsScalar) : MultFor :=
  multiplicity_assembly_holds hP injective_decomposition_action_holds.1 hc_decomposition_levi_holds injective_decomposition_action_holds.2.2 hLS hLR hSC hCC h4 h5

end PositivityTheory.RgBcC.RealD
