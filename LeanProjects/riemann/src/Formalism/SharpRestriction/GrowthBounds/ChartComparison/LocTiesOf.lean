import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocCore
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocMore
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.WtTieOf

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m)
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

set_option maxHeartbeats 2000000 in

structure LocTiesR (Fo : FormsIn M (i + 1) hi) (Lc : LocIn X u w hg Lv i Fo.Ch) (e : D.what₂.LL →+* (D.gat u w hg).Kf) (β : Fo.Ch) :
    Prop where
  frRat : FrRatJ (Lc.t β) Lc.B
  sameU : SameUlocJ hi (Fo.K β).lev (Lc.Uloc β)
  hypT : HypTJ (Lc.t β)
  bad_p : ∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal
  std : cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E Lc.B).1 * gramN D (i + 1) hi *
    (reGL (rankN D (i + 1) hi) D.host.E Lc.B).1 = 1
  psi : UnitCharacterChartCompatibility hi (Fo.K β).lev e (Lc.ψ β)
  chiRat : ChiRatAll (Fo.K β).lev D.what₂.embLL
  chRat : ∀ cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)

set_option maxHeartbeats 8000000 in

theorem locTies_of {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D} (K : CmpTied D X T Gt c)
    (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) {Fo : FormsIn M (i + 1) hi} {Lc : LocIn X u w hg Lv i Fo.Ch} {β : Fo.Ch}
    (H : LocTiesR hi Fo Lc (c.embW u w hg) β) : LocTies hi Fo Lc (Gt.gat_pos u w hg) (c.embW u w hg) β where
  frRat := H.frRat
  sameU := H.sameU
  hypT := H.hypT
  bad_p := H.bad_p
  std := H.std
  pos_emb := fun v s x => locJ_pos_emb hi (Lc.t β) Lc.B K v s x
  wt := StepIn.wt_of (M := M) Gt w hg Lv ht hF i hi (stepInOf hi Fo Lc (Gt.gat_pos u w hg)) rfl β
  psi := H.psi
  chiRat := H.chiRat
  chRat := H.chRat

theorem core_of_R {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D} (K : CmpTied D X T Gt c)
    (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) {Fo : FormsIn M (i + 1) hi} {Lc : LocIn X u w hg Lv i Fo.Ch} {β : Fo.Ch}
    (H : LocTiesR hi Fo Lc (c.embW u w hg) β) : (stepInOf hi Fo Lc (Gt.gat_pos u w hg)).Core (c.embW u w hg) β :=
  core_of hi (locTies_of hi K ht hF H)

theorem iwF_of (Fo : FormsIn M (i + 1) hi) (Lc : LocIn X u w hg Lv i Fo.Ch)
    (pos : (Σ v : Fin (Fl.Pj (i + 1)).nV, Fin ((Fl.Pj (i + 1)).n' v)) ≃ D.what₂.Tau) (β : Fo.Ch) :
    (stepInOf hi Fo Lc pos).IwF β :=
  fun v a => locJ_iw_F hi (Lc.t β) Lc.B v a

end Formalism.MainNotions.G.CmpJ

end
