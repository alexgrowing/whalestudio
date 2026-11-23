import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InHHClassFin
import Formalism.PeriodIntegrals.InHHClassFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.PoincareInHH Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Closed

section

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem WuDefinite_holds : Formalism.L2.SG.PoincareInHH.Cut.WuDefinite X u := by
  first
  | exact Formalism.L2.SG.PoincareInHH.Cut.wuDefinite_holds X u
  | exact Formalism.L2.SG.PoincareInHH.Cut.wuDefinite_holds (X := X) (u := u)

theorem ClassFin_holds (hK : X.LevelSubgroupCharacter) : Formalism.L2.SG.PoincareInHH.Cut.ClassFin X u hK := by
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  exact stabClassFinite X.B.I (fixSet X u) (WuDefinite_holds X u) (Ku X u hK) X.B.g (X.xu u) hg
    (fun h hh => ((Formalism.L2.SG.Closed.level_subgroup_properties X).1 _ hh).1)

theorem ColBound_holds (hK : X.LevelSubgroupCharacter) : Formalism.L2.SG.Pf.ColBound X u hK := by
  first
  | exact Formalism.L2.SG.Pf.colBound_of X u hK (ClassFin_holds X u hK)
  | exact Formalism.L2.SG.Pf.colBound_of (X := X) (u := u) hK (ClassFin_holds X u hK)

theorem OmCover_holds (I : AutInst) : Formalism.L2.SG.Pf.OmCover I := by
  first
  | exact Formalism.L2.SG.Pf.omCover_holds I
  | exact Formalism.L2.SG.Pf.omCover_holds (I := I)

theorem MultPoly_holds : Formalism.L2.SG.PoincareInHH.Cut.MultPoly X :=
  Formalism.L2.SG.Pf.multPoly_holds_of'' X (OmCover_holds _)

end

end Formalism.L2.SG.Closed
