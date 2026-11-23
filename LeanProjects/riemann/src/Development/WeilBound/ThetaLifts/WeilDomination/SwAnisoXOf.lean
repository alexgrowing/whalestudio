import Development.WeilBound.ThetaLifts.LatticeBasics.SiegelWeilAnisoOf

namespace PositivityTheory.ThKClose

open GlobalTheory.ThK.Dbl

theorem swAnisoX_of (h1 : SiegelWeilStd) (h2 : FrameConj) (hL : FinLevel) (hC : Stab2Cpt) : SWAnisoX :=
  (siegelWeilAniso_of h1 h2 hL hC).2

end PositivityTheory.ThKClose
