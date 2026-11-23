import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.StdSub
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescFOfValRatF
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianColumns.BaseModelLevelEq
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsGat
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsRec
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField Formalism.L2.Forms

namespace Formalism.L2.G

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

def ExtOf.map (X : ExtOf Os Ks O Kf) (eO : O ≃+* O') (eK : Kf ≃+* Kf')
    (hc : ∀ x, eK (algebraMap O Kf x) = algebraMap O' Kf' (eO x)) (hfrac : IsFractionRing O' Kf')
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal O') O') : ExtOf Os Ks O' Kf' where
  φ := (eO : O →+* O').comp X.φ
  φK := (eK : Kf →+* Kf').comp X.φK
  comm := by
    intro x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [X.comm, hc]
  fin := (RingHom.Finite.of_surjective _ eO.surjective).comp X.fin
  frac := hfrac
  complete := hcomp

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

def RingCompatibleAt (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV) : Prop :=
  ∃ (eW : WQ (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) ≃+* (D.gat u w hg).P.W v)
    (eQ : QQ (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) ≃+* (D.gat u w hg).P.Qq v)
    (eO : ORec D w ((D.gat u w hg).P.n' v) ≃+* (D.gat u w hg).O)
    (eK : KfRec D w ((D.gat u w hg).P.n' v) ≃+* (D.gat u w hg).Kf),
    (∀ x, eQ (algebraMap _ _ x) = algebraMap ((D.gat u w hg).P.W v) ((D.gat u w hg).P.Qq v) (eW x)) ∧
    (∀ x, eK (algebraMap _ _ x) = algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (eO x)) ∧
    (∀ y, (D.gat u w hg).P.ι v (eQ y) =
      eK ((extRec D w ((D.gat u w hg).P.n' v)).φK (iota (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) y))) ∧
    (∀ x, (D.gat u w hg).P.j v (eW x) =
      eO ((extRec D w ((D.gat u w hg).P.n' v)).φ (jO (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) x))) ∧
    eO ((extRec D w ((D.gat u w hg).P.n' v)).φ (wU (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v))) = (D.gat u w hg).P.w

theorem stdSubAt_of_ring (D : D7) (h : ∀ u w hg v, RingCompatibleAt D u w hg v) : Joints.StdSubAt D := by
  intro u w hg v
  obtain ⟨eW, eQ, eO, eK, hWQ, hOK, hι, hj, hw⟩ := h u w hg v
  have hD := (D.gat u w hg).P.setting v
  exact stdSub_of_iso hD eW eQ hWQ
    ((extRec D w ((D.gat u w hg).P.n' v)).map eO eK hOK hD.frac_O hD.complete_O) hι hj hw

def GatIs (D : D7) (H : LevelData D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Prop :=
  ∃ (W Qq O Kf : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field Qq) (_ : Algebra W Qq)
    (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf)
    (n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w0 : O)
    (hS : Formalism.MainNotions.G.HidaSetting (D.what₂.places.resChar w) n' W Qq O Kf ι σ j w0) (nV r m : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = D.R.k)
    (I : LocId (H u) (D.what₂.places.resChar w) nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ (H u) (D.what₂.places.resChar w) →* Oˣ)
    (e : ℕ), Cmp.HypAtP I ∧ D.gat u w hg = gatOfLevelP (H u) hS nV r lam0 dom hk I ψ e

theorem gatE_of_gatIs (D : D7) (H : LevelData D) (hT : ∀ u, Cmp.TrivStabU (H u))
    (h : ∀ u w hg, GatIs D H u w hg) : TrivialStabiliserFiniteClasses D := by
  intro u w hg
  obtain ⟨W, Qq, O, Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e, hH, heq⟩ :=
    h u w hg
  rw [heq]
  exact ⟨Cmp.trivStab hS r lam0 dom hk I ψ e (isUnit_det_gram0 D.sp) hH (hT u),
    Cmp.finClasses hS r lam0 dom hk I ψ e (isUnit_det_gram0 D.sp) hH⟩

structure GroupCompatibilityAll (D : D7) (Gt : GatTies D) (c : LatCmp D) where

  herm : Formalism.L2.Herm.Herm0 D

  forms : ∀ u : D.what₂.Word, Forms0 D u

  cmp : Cmp.CmpTied D herm forms Gt c

  ring : ∀ u w hg v, RingCompatibleAt D u w hg v

  gat : ∀ u w hg, GatIs D herm.lev0 u w hg

def GroupCompatibilityFamily {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => ∀ hx : Fm.x1 < x, Nonempty (GroupCompatibilityAll (Fm.D x i) (Fm.gatT x i) (Fm.ex x hx i).cmp)

end Formalism.L2.G
