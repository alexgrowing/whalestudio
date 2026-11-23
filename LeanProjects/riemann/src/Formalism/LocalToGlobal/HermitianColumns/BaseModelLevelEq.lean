import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Herm0 (D : D7) where

  lev0 : LevelData D

  g : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), GLevTie (lev0 u) (D.gat u w hg)

def FullTied.to0 {D : D7} (X : FullTied D) : Herm0 D := ⟨X.base.lev0, X.g⟩

theorem FullTied.base_model_level_eq {D : D7} (X : FullTied D) : X.to0.lev0 = X.base.lev0 := rfl

theorem FullTied.base_model_g_eq {D : D7} (X : FullTied D) : X.to0.g = X.g := rfl

end Formalism.L2.Herm
