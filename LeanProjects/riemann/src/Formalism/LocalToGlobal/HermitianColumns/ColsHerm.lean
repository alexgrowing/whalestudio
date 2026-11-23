import Formalism.LocalToGlobal.HermitianColumns.CompletionIntegersIff
import Formalism.LocalToGlobal.HermitianColumns.Lev0Tied
import Formalism.LocalToGlobal.HermitianColumns.ClsNonempty
import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter
import Formalism.LocalToGlobal.HermitianColumns.StepLevelQ
import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GTied (D : D7) (H : HermTied D) : Type :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    GLevTie (H.lev0 u) (D.gat u w hg)

structure FullTied (D : D7) extends AllTied D where
  levelZeroCompatibility : Lev0Tied D base.toHermCols atT
  g : GTied D base
  ad : AdTied D base.toHermCols atT
  cof : CofTied D base.toHermCols atT
  piG : PiGConst D base.toHermCols atT levelZeroCompatibility
  stabMap : StabMapTied D base.toHermCols atT
  fvI : FvStepTied D base.toHermCols atT
  relDet : RelativeDeterminantCompatible D base
  std : StdTied D
  vpos : PositiveVolumeCompatible D
  baseL : BaseTied D base.toHermCols atT

structure ColsHerm (D : D7) where
  base : HermCols D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  levelZeroCompatibility : Lev0Tied D base atT
  ad : AdTied D base atT
  cof : CofTied D base atT
  piG : PiGConst D base atT levelZeroCompatibility
  stabMap : StabMapTied D base atT
  fvI : FvStepTied D base atT
  std : StdTied D
  baseL : BaseTied D base atT

def FullTied.cols {D : D7} (X : FullTied D) : ColsHerm D where
  base := X.base.toHermCols
  atT := X.atT
  levelZeroCompatibility := X.levelZeroCompatibility
  ad := X.ad
  cof := X.cof
  piG := X.piG
  stabMap := X.stabMap
  fvI := X.fvI
  std := X.std
  baseL := X.baseL

end Formalism.L2.Herm

end
