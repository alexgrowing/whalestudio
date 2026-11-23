import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieSurj
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
import Formalism.LocalToGlobal.GroupLattices.FockModels.Sandwich
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StabilizerCount

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem htupW_le_htup (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : (D.gat u w hg).P.Tup) :
    (D.gat u w hg).P.HtupW L ≤ (D.gat u w hg).P.Htup L := by
  have hW := Formalism.MainNotions.G.Joints.weylSandwich_of_model D (Formalism.L2.G.Model.modelSandwichG_of_ties D Gt)
  refine Submodule.span_mono ?_
  rintro Z ⟨F, hF, rfl⟩
  refine ⟨F, fun v => ?_, rfl⟩
  refine (Submodule.span_mono ?_ : HtenW (D.gat u w hg).O _ _ ≤ Hten (D.gat u w hg).O _ _) (hF v)
  rintro Y ⟨F', hF', rfl⟩
  exact ⟨F', fun s => (hW u w hg _ _ _).2 (hF' s), rfl⟩

theorem m_le_mna (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : (D.gat u w hg).M ≤ (D.gat u w hg).Mna := by
  intro F hF
  have h1 := (mem_funMod_iff (D.gat u w hg) (D.gat u w hg).P.HtupW F).1 hF
  refine (mem_funMod_iff (D.gat u w hg) (D.gat u w hg).P.Htup F).2 fun i => ?_
  exact ⟨fun L hL => htupW_le_htup Gt u w hg L ((h1 i).1 L hL), (h1 i).2⟩

theorem m_finite_rec (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (h : (D.gat u w hg).FinClasses) :
    Module.Finite (D.gat u w hg).O (D.gat u w hg).M :=
  Formalism.MainNotions.FormalGroupSystem.Pf.m_finite (D.gat u w hg) h (m_le_mna Gt u w hg)

variable {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

theorem surjRat_rec (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I) :
    SurjRat T Gt I :=
  surjRat_pf H hloc (fun u w hg => frac_of_gatIs X.lev0 u w hg (hG u w hg))
    (fun u w hg => m_finite_rec Gt u w hg (finClasses_of_gatIs X.lev0 u w hg (hG u w hg)))

theorem comparison_lattice_span_eq (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).O
      (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M :=
  latM_rec' H hG hloc (surjRat_rec H hG hloc) u w hg

theorem cmpHyp0P_of_cmpCore (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I) :
    CmpHyp0P T Gt I where
  ex := H.ex
  evInj := fun u w hg => evInj_rec Gt I u w hg
  ptEx := fun u w hg => ptEx_rec X T u w hg I.B
  ptAll := fun u w hg => ptAll_rec X T u (H.same u) w hg I.B
  chi := H.chi
  latM := comparison_lattice_span_eq H hG hloc

end Formalism.L2.G
