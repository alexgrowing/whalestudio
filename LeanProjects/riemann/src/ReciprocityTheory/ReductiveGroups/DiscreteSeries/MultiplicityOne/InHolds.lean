import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergHaarFactsHold
import Formalism.FormalDegreeBessel.FinalG

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem multiplicity_one_hypotheses_hold : UnitaryGroupStructuralFacts :=
  ⟨ReciprocityTheory.ChartRestriction.DS.Xi.heisenbergHaarFacts_hold,
    Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists,
    Formalism.FourierDecayAlt.P.b2_rank_one_coord,
    Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization,
    Formalism.FourierDecayAlt.P.unipotent_weyl_properties,
    Formalism.FourierDecayAlt.P.conjugation_preserves_haar,
    Formalism.FourierDecayAlt.P.lemma_b_from_xi,
    Formalism.FourierDecayAlt.P.orbital_integral_ae_convergence_continuity,
    Formalism.FourierDecayAlt.P.phase_function_bound,
    Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear,
    Formalism.FourierDecayAlt.P.regularised_average_identity,
    Formalism.FourierDecayAlt.P.unfolding_identity_of_integration_formula,
    Formalism.FourierDecayAlt.P.ae_equality_from_test_functions,
    Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting,
    Formalism.FourierDecayAlt.P.normalisation_unique_every_setting,
    Formalism.QuantumDeterminants.uWNormal,
    Formalism.QuantumDeterminants.ellAdd,
    Formalism.QuantumDeterminants.nSubgroup⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
