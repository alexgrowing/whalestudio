import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Lev0Data (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) where
  A : LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w h)
  J : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E
  Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))

def lev0AtOf {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}
    (K : CmpTied D X T Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Lev0Data D u w h where
  A := locAt X u w h K.B
  J := gramN D 0 (Nat.zero_le _)
  Lb := (T u).cls0.lev.Lb
  Uloc := (T u).cls0.lev.Uloc

def lev0At {D : D7} {Gt : GatTies D} {c : LatCmp D} (Gd : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Lev0Data D u w h :=
  lev0AtOf Gd.cmp u w h

def lev0AtOf_compatible {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}
    (K : CmpTied D X T Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    CmpTie ((T u).cls0).lev (embT D) D.what₂.embLL (tEL D) (D.gat u w h) (c.embW u w h)
      (lev0AtOf K u w h).A (Gt.gat_pos u w h)
      (fun x cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z))
      ((T u).cls0).y (c.cmp u w h) :=
  K.tie u w h

theorem lev0AtOf_lev {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}
    (K : CmpTied D X T Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (lev0AtOf K u w h).J = gramN D 0 (Nat.zero_le _) ∧ (lev0AtOf K u w h).Lb = (T u).cls0.lev.Lb ∧
      (lev0AtOf K u w h).Uloc = (T u).cls0.lev.Uloc :=
  ⟨rfl, rfl, rfl⟩

theorem lev0AtOf_joint {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}
    (K : CmpTied D X T Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hJ : Joint0 X.lev0 u (T u)) :
    (lev0AtOf K u w h).Lb = reL (rank_eq_first_level D.R) (X.lev0 u).Lb ∧
      ∀ v, (lev0AtOf K u w h).Uloc v = ((X.lev0 u).Uloc v).map (reGL (rank_eq_first_level D.R) _).toMonoidHom :=
  ⟨hJ.Lb_eq, hJ.Uloc_eq⟩

theorem gram_level_zero_eq_reindex (D : D7) :
    gramN D 0 (Nat.zero_le _) = D.sp.gram0.reindex (finCongr (rank_eq_first_level D.R)) (finCongr (rank_eq_first_level D.R)) := by
  ext i j
  simp [gramN, Spaces.gram0, Matrix.reindex_apply]

end Formalism.L2.PairingIndexBounds.F

end
