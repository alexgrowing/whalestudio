import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
import Formalism.CMTypeGalois.CMTypeFrobenius.MQFrob
import Formalism.CMTypeGalois.CMTypeFrobenius.KroneckerMeaning
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesA
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesB
import Mathlib
import Formalism.CMTypeGalois.CMTypeFrobenius.HostFrob
import Formalism.CMTypeGalois.CMTypeFrobenius.HostConj
import Formalism.CMTypeGalois.CMTypeFrobenius.HostInertia
import Formalism.CMTypeGalois.CMTypeFrobenius.HostMu
import Formalism.CMTypeGalois.CMTypeFrobenius.HostEmb

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois
theorem mqFrob : MQFrob := mqFrob_of mqGalois
theorem hostGalois : HostGalois := hostGalois_of mqGalois mqKummer
theorem hostFrob : HostFrob := hostFrob_of mqFrob hostGalois kroneckerMeaning
theorem hostConj : HostConj := hostConj_of hostGalois mqKummer
theorem hostInertia : HostInertia := hostInertia_of hostGalois mqGalois
theorem hostMu : HostMu := hostMu_of mqKummer hostGalois
theorem hostEmb : HostEmb := hostEmb_of hostConj hostGalois

end Formalism.Q3
