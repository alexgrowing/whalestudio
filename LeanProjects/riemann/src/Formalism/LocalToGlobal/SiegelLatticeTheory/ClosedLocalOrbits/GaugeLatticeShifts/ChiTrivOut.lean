import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNHomPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.VanishNConj
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.TermOp.Vanish

theorem nilradical_conj_level' : NilradicalConjLevel :=
  nilradical_conj_level_of_mem fun _ X u => unipotent_in_level X u

theorem chiTrivialC_outright : ChiTrivialC := chiTrivialC_of_nconj nilradical_conj_level'

theorem lemmaVC_of_rest (hA : AvgCore) (h3 : RCocompactC) (h4 : NonRelCharC) : Formalism.L2.SG.Full.LemmaVC :=
  lemmaVC_of_nconj hA nilradical_conj_level' h3 h4

end Formalism.L2.SG.Pf
