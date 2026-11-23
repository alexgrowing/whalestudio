import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.FillInstRecEqWj

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

set_option maxHeartbeats 4000000 in

theorem gatIs_recG (H : LevelData (recG D sc Ce Lc X hd)) (hL : ∀ u, H u = Lc u)
    (hH : ∀ u w h, Cmp.HypAtP (X u w h).I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : GatIs (recG D sc Ce Lc X hd) H u w hg := by
  unfold GatIs
  rw [hL u]
  exact ⟨(X u w hg).W, (X u w hg).Qq, (X u w hg).O, (X u w hg).Kf, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
    (X u w hg).ι, (X u w hg).σ, (X u w hg).j, (X u w hg).w, (X u w hg).hS, _, _, _, _, _, _, (X u w hg).I, (X u w hg).ψ, _,
    hH u w hg, rfl⟩

end Formalism.L2.G
