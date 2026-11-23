import Formalism.LocalToGlobal.CharacterGerms.RowTiePHaSpan
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHaLeaves

set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem descent_span : DescSpanSt Xo c :=
  descSpanSt_of (HaP.haSpanSt_of HaP.satRetr HaP.rowInvUp)

end Formalism.L2.FormalSeriesBounds
