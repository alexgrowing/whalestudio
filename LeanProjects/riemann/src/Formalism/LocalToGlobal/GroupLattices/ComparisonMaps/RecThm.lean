import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.FramesTr

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

theorem embFr_inj (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) : Function.Injective (embFr T u) := by
  have hinj : Function.Injective ((D.fm u).emb 0) := by
    exact (D.fm u).emb_inj 0
  intro x y h
  simp only [embFr, LinearMap.coe_mk, AddHom.coe_mk] at h
  apply hinj
  funext cl z
  have h4 := congrFun (congrFun h cl) ((T u).val0.eY z)
  simpa using h4

structure CmpHyp0 (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  evInj : ∀ u w hg, EvInj (embT D) (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg)
    (J := gramN D 0 (Nat.zero_le _))

  ptEx : ∀ u w hg, PtEx ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B)
    ((T u).cls0).y

  ptAll : ∀ u w hg, PtAll ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B)
    ((T u).cls0).y

  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  latM : ∀ u w hg, Submodule.span (D.gat u w hg).O
    (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M

theorem CmpHyp0.toHyp {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X} (H : CmpHyp0 T Gt I) :
    CmpHyp T Gt I where
  ex := H.ex
  uniq := fun u w hg => valUniq_of (embT_conj D) (H.evInj u w hg) (H.ptEx u w hg)
  pos := H.pos
  chi := H.chi
  li := fun u w hg => cmpC_li (e := I.embW u w hg) (embT_conj D) (H.ex u w hg)
    (valUniq_of (embT_conj D) (H.evInj u w hg) (H.ptEx u w hg)) (H.ptAll u w hg) (embFr_inj T u)
    ((D.fm u).lat 0).b ((D.fm u).lat 0).b.linearIndependent
  latM := H.latM

end Formalism.L2.G.Cmp

end
