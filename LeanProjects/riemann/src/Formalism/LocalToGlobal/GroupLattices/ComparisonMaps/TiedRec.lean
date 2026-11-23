import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.LocalToGlobal.HermitianColumns.BaseModelLevelEq
import Formalism.LocalRingCardinality.DataLatDefs

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def tEL (D : D7) : D.what₂.Tau → D.host.E →+* D.what₂.LL :=
  fun τ => D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

theorem tEL_emb (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (tEL D τ x) = embT D τ x := by
  simp only [tEL, embT, Formalism.BasicNotions.Host.emb, RingHom.comp_apply]
  first
    | exact RingHom.congr_fun D.embE_φ₀ _
    | exact D.embE_φ₀ _
    | (rw [← D.embE_φ₀]; rfl)

def locAt (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w hg) where
  rk := (X.g u w hg).rk.trans (rank_eq_first_level D.R)
  pl := (X.g u w hg).pl
  eQ := fun v => (X.g u w hg).eQ v _ rfl
  spl := fun v => (X.g u w hg).spl _ ((X.g u w hg).pl v).2
  B := reGL (rank_eq_first_level D.R) _ B
  yG := fun i => reGL (rank_eq_first_level D.R) _ ((X.g u w hg).yG i).1
  gamI := fun i => (reGL (rank_eq_first_level D.R) D.host.E).toMonoidHom.comp
    ((UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0).subtype.comp ((X.g u w hg).gamI i))

def FrRat (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (X.g u w hg).fr w' h =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

def StdB (D : D7) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  cT (sigD D : D.host.E →+* D.host.E) (reGL (rank_eq_first_level D.R) D.host.E B).1 * gramN D 0 (Nat.zero_le _) *
      (reGL (rank_eq_first_level D.R) D.host.E B).1 = 1 ∧
  ∀ x : Fin (D.R.N 0) → D.host.E, x ∈ selfDualLatticeCoords D 0 (Nat.zero_le _) ↔
    ∀ a, (((reGL (rank_eq_first_level D.R) D.host.E B)⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 *ᵥ x) a ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range

set_option maxHeartbeats 1000000 in

structure CmpTied (D : D7) (X : Formalism.L2.Herm.Herm0 D) (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D)
    (c : LatCmp D) where

  B : GL (Fin D.R.k) D.host.E
  B_std : StdB D B

  fr_B : ∀ u w hg, FrRat X u w hg B
  tie : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    CmpTie ((T u).cls0).lev (embT D) D.what₂.embLL (tEL D) (D.gat u w hg) (c.embW u w hg)
      (locAt X u w hg B) (Gt.gat_pos u w hg)
      (fun x cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z))
      ((T u).cls0).y (c.cmp u w hg)

theorem CmpTied.val_rat {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}
    (K : CmpTied D X T Gt c) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : ((D.fm u).lat 0).V)
    (i : (D.gat u w hg).comp) (L : (D.gat u w hg).P.Tup) (hL : (D.gat u w hg).P.IsLatTup L) :
    c.cmp u w hg x i L ∈ Set.range
      (MvPolynomial.map (c.embW u w hg) : XR (D.gat u w hg).P D.what₂.LL → (D.gat u w hg).P.Xsp) :=
  (K.tie u w hg).val_rat x i L hL

end Formalism.L2.G.Cmp

end
