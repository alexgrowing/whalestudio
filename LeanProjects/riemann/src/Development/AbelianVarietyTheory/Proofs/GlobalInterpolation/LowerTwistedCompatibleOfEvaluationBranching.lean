import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PerQ

theorem lowerTieTwAt_to_lib : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup),
    GlobalTheory.PerQ.LowerTieTwAt D T u μ → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D T u μ := by
  rintro D T u μ ⟨a, b, P, hP⟩
  exact ⟨a, b, ⟨P.br, P.coM, P.coP, P.Pt_eq, P.lat_co, P.pt_co⟩, hP⟩

end GlobalTheory.PerQ
