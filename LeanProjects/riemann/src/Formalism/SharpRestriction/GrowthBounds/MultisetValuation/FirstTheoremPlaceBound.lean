import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaApplyDScale
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmRestNormOfPlace
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveSecondVariable

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem ea_restSU (hG : RestGc p) : ea_RestSU X Y :=
  ea_restSU_of X Y (ea_restSExpV_of X (restBeta p) (th_restGcV_of X hG))

theorem first_theorem_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : EntryBoundOfHypotheses X Y D :=
  fun hA v j hj =>
    ea_A1U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem second_lemma_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : PlacewiseLowerBoundEvenShift X Y D :=
  fun hA v j hj =>
    ea_A2U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem hecke_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : RestBU X Y D :=
  fun hA v j hj i hi =>
    ea_BU D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brScale X) (ea_brClass X) (ea_brNum X) hA v j hj i hi

end Formalism.MainNotions.FormalGroupSystem.Pf
