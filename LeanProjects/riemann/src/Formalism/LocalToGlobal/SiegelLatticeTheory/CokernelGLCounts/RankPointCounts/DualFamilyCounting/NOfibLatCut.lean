import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DictLatF : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 → LatQ X (Xq X n) (xq X n) (Mq X n)

def DictLatB : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → LatQ X (Xq X n) (xq X n) (Mq X n) → Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0

theorem dictLat_of (hF : DictLatF) (hB : DictLatB) : DictLat :=
  fun X u n hn => ⟨hF X u n hn, hB X u n hn⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
