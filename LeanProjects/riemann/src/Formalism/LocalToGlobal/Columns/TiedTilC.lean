import Formalism.LocalToGlobal.Columns.TiedTilB
import Formalism.LocalToGlobal.Columns.TiedXpU

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

theorem tilMove (hS : SpStd d.toColBase) (hP : PtSurjP d) (hQ : PtSurj d) (u : d.what₂.Word) : TilMove a u :=
  fun c => til_tmv_rec a hS hP hQ u c

end Formalism.L2.Col
