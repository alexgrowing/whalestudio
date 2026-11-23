import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpLApply
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embFr (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) :
    ((D.fm u).lat 0).V →ₛₗ[D.what₂.embLL] ((D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ) where
  toFun x := fun cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z)
  map_add' x y := by funext cl z; rw [map_add]; rfl
  map_smul' a x := by funext cl z; rw [LinearMap.map_smulₛₗ]; rfl

structure CmpIn (D : D7) (X : Formalism.L2.Herm.Herm0 D) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  B : GL (Fin D.R.k) D.host.E
  B_std : StdB D B
  fr_B : ∀ u w hg, FrRat X u w hg B

variable {X : Formalism.L2.Herm.Herm0 D}

def cmpRec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V → (D.gat u w hg).Fn :=
  cmpC ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg) (I.embW u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

structure CmpHyp (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  uniq : ∀ u w hg, ValUniq ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (fun a => cmpRec T Gt I u w hg (((D.fm u).lat 0).b a))

  latM : ∀ u w hg, Submodule.span (D.gat u w hg).O
    (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M

def latCmpC (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) : LatCmp D where
  embW := I.embW
  embW_int := I.embW_int
  cmp := fun u w hg => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).toAddMonoidHom
  cmp_smul := fun u w hg a x => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).map_smulₛₗ a x
  cmp_li := H.li
  cmp_M := H.latM

def latticeComparisonCompatible (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) :
    CmpTied D X T Gt (latCmpC T Gt I H) where
  B := I.B
  B_std := I.B_std
  fr_B := I.fr_B
  tie := fun u w hg => cmpC_tie (tEL D) (H.ex u w hg) (H.pos u w hg) (H.chi u w hg)

end Formalism.L2.G.Cmp

end
