import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValUniqOf
import Formalism.SharpRestriction.GrowthBounds.DataGChain

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G

variable {p : ℕ} {G : GAtP p} {Fl : Fills G}

instance compFintype (Lv : Levels Fl) : ∀ j, Fintype (Lv.comp j)
  | 0 => G.finComp
  | j + 1 => Lv.finS j

abbrev gatJ (Lv : Levels Fl) (j : ℕ) : GAtP p where
  O := G.O
  Kf := G.Kf
  P := Fl.Pj j
  comp := Lv.comp j
  finComp := compFintype Lv j
  lev := Lv.lev j
  e := G.e

end Formalism.L2.G.Cmp

end
