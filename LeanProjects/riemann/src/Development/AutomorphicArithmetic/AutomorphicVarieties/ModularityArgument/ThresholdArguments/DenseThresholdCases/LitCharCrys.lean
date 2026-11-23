import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularityOfHyps

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.Lit.hecke_ladic_char_crystalline_of_de_rham_pst_wd_llc (h1 : GlobalTheory.Published.HeckeLAdicCharacterDeRham) (h2 : GlobalTheory.Published.DeRhamPotSemistable)
    (h3 : GlobalTheory.Published.AlgebraicCharacterWD) : GlobalTheory.Published.HeckeLAdicCharacterCrystalline :=
  _root_.GlobalTheory.Published.CharCrysModel.of_hypotheses_m_alt_alt h1 h2 h3
end
