import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs

namespace Formalism.L2.Pj

open Formalism.BasicNotions

theorem exists_par_pins_of_rec (D : D7) (hF : OFull D) (hz : OZeta D) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab) :
    ∃ Q : Par D, Q.Pins :=
  exists_parameter_conditions D hF hz (fun j hj => ⟨datInt_of Formalism.IndefR.Fin.factPrincipalDatum D j,
    ⟨efW_unimod_of Formalism.IndefR.Fin.factPrincipalDatum D j _, latW_rank D j hj, datDom_holds D j hj _⟩⟩) hN

end Formalism.L2.Pj
