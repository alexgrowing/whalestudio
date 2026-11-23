import Formalism.LocalToGlobal.CharacterGerms.UnitSeriesFrobenius
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace UnitSeriesProduct

open PartialDerivEval

section Inv

variable {C : Type} [Field C] {V : VF C}

end Inv

section Exp

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

end Exp

section Geo

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

abbrev NN (k : ℕ) : Pt C 2 dd := comp1 (Y.nmul k) (pt C dd 1)

abbrev AA (k : ℕ) : Fin 3 → Pt C 2 dd := ![pt C dd 0, NN Y k, pt C dd 1]

abbrev HH (P : Pt C 2 dd) : PS C 2 dd := ev ![pt C dd 0, P] Y.h

end Geo

end UnitSeriesProduct

end Formalism.L2.FormalSeriesBounds
