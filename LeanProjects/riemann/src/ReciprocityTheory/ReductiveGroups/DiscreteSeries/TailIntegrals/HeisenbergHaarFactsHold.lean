import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarScaling

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem heisenbergHaarFacts_hold : InductiveHeisenbergInputs :=
  ⟨Formalism.FourierDecayAlt.P.stabilizer_integration_formula,
    Formalism.FourierDecayAlt.P.rank_one_coordinates_formula,
    Formalism.FourierDecayAlt.P.stabilizer_one_parameter_mem,
    Formalism.FourierDecayAlt.P.unipotent_haar_recursion,
    Formalism.FourierDecayAlt.P.unipotent_haar_base_case,
    Formalism.FourierDecayAlt.P.heisenberg_conjugation_by_levi,
    Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure,
    Formalism.FourierDecayAlt.P.heisenberg_inverse,
    Formalism.FourierDecayAlt.P.heisMul_statement,
    Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent,
    Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed,
    Formalism.FourierDecayAlt.P.heisenberg_haar_measure,
    Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting,
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact,
    Formalism.FourierDecayAlt.P.norm_power_integrable_sharp,
    Formalism.FourierDecayAlt.P.matrix_norm_ge_one,
    Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar,
    Formalism.FourierDecayAlt.P.haar_measure_inversion,
    Formalism.FourierDecayAlt.P.compact_group_haar_exists,
    Formalism.FourierDecayAlt.P.unitary_group_closed,
    Formalism.FourierDecayAlt.P.unipotent_radical_closed,
    Formalism.FourierDecayAlt.P.weyl_subgroup_closed,
    Formalism.FourierDecayAlt.P.levi_haar_measure_exists,
    Formalism.FourierDecayAlt.P.weyl_haar_exists,
    Formalism.FourierDecayAlt.P.unipotent_haar_exists,
    Formalism.FourierDecayAlt.P.unitary_group_haar_exists,
    Formalism.FourierDecayAlt.P.heisenberg_action_formula⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
