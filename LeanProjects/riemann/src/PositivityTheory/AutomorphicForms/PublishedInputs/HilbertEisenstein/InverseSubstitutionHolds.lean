import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SecondCountableTopologyUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

theorem inverse_substitution_holds : InvSubst := by
  intro F _ _ v f t
  exact MultiplicativeHaarInverse.inv_subst f t

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
