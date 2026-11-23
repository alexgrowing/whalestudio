import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction
import Formalism.LocalToGlobal.GroupLattices.Joint0

noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.MainNotions.RT Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

def UpMatchAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), UpDiaMatch0F T

def DnMatchAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), DnDiaMatch0F T

theorem crossDia0_of_forms0 {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (hU : UpDiaMatch0F T)
    (hD : DnDiaMatch0F T) : CrossDia0 D u :=
  fun v v' h φ hφ a => ⟨diamond_commutes_U_distinct T hU v v' h a φ hφ, diamond_commutes_D_distinct T hD v v' h a φ hφ⟩

theorem crossDia0T_of (hU : UpMatchAll) (hD : DnMatchAll) (D : D7) (u : D.what₂.Word) : CrossDia0T D u := by
  rintro ⟨Ch, chOf, T, -⟩ _ _
  exact crossDia0_of_forms0 T.to0 (hU D u T.to0) (hD D u T.to0)

end CrossDiaZero

end
