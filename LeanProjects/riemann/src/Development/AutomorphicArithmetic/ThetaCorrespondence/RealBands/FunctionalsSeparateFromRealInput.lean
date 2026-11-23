import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPeriod
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.Separate

namespace UpperTheory.Lit

theorem functionalsSeparate_of_input
    (P : GlobalTheory.FunPr.Hypotheses₂) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := GlobalTheory.T.level_models_of_functoriality P
  have rowStep := GlobalTheory.T.level_induction_from_pairs P (GlobalTheory.T.pair_existence_of_functoriality P) rowModels
  have rowTower := GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow rowModels rowStep
  have conv := GlobalTheory.T.level_tower_convergence P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := GlobalTheory.T.theta_surjective_definite_level P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps GlobalTheory.T.largeScaleSizes_imply_gapConditions (GlobalTheory.T.basic_models_of_functoriality P) (GlobalTheory.T.level_tower_rapid_decay P rowTower) per onto
    (GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data GlobalTheory.T.dependence_fixed)
  exact separate_of_steps_gap P rowTower GlobalTheory.T.largeScaleSizes_imply_gapConditions GlobalTheory.T.goodRows_principalLevel_are_rows conv weak

end UpperTheory.Lit
