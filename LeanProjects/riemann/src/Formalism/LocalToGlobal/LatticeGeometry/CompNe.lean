import Formalism.LocalToGlobal.LatticeGeometry.NormDetInf
import Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef
import Formalism.LocalToGlobal.LatticeGeometry.AmpleOnAbelianBase

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

structure ShimU (D : D7) (G : DV.Geo D.what₂.LL) {Lev : Type}
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg) (w : Dat D Lev) where

  Comp : Type
  [compFin : Fintype Comp]
  [compNe : Nonempty Comp]

  cx : CxPkg D.what₂.Tau w.N w.j Comp

  alg : AlgPkg G D.what₂.Tau w.N Comp

  pad : PadPkg D w.N w.j Comp jC ng

attribute [instance] ShimU.compFin ShimU.compNe

end Formalism.L2.Geo
