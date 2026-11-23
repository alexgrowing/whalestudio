import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SysC
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCoefficients
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

theorem oddDeg_of_vt (X : Sys p) (j : ℕ) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).Vtup) : OddDeg X j G := by
  classical
  intro m hm b hb
  obtain ⟨d, hd, hw⟩ := vtOddDeg X j G hG b.1 b.2 hb
  have h1 : Finsupp.weight (wBk X j b.1 b.2) m = d := hw (MvPolynomial.mem_support_iff.1 hm)
  rw [← hd, ← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold wBk blkJ
  by_cases hx : (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = b
  · have hx' : (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨b.1, b.2⟩ := hx
    rw [if_pos hx, if_pos hx']
    simp
  · have hx' : ¬ (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨b.1, b.2⟩ := hx
    rw [if_neg hx, if_neg hx']
    simp

def GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (G : (X.Pj j).Xsp) : Prop :=
  GoodG X Kc j G ∧ OddDeg X j G

theorem vtIn_GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] : VtIn X (GdC X Kc) :=
  fun j G hG => ⟨vtGood X Kc j G hG, oddDeg_of_vt X j G hG⟩

theorem delEquivOn_GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] :
    DelEquivOn X Kc (GdC X Kc) :=
  fun j A G f hG => (delEquivH X Kc j A G f hG.1 hG.2).2

structure CEmbC (G : GAtP p) extends CEmb G where
  rd : ∀ v, G.P.W v →+* WW p
  compat : Compat G toCEmb rd

variable (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

abbrev pendT : Pend X := pendR X E.toCEmb hfin hst (beLT hLT) (thFOf X pos F)

theorem adm6_pendT (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm6 D X (pendT X E hfin hst hLT pos F) := up_down_adjoint D X _

theorem invariance_of_stable_geometry (D : Formalism.BasicNotions.D7) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E.toCEmb
    StabGeo X ℂ_[p] hfin (thFOf X pos F) → KapStab X ℂ_[p] → Formalism.MainNotions.FormalGroupSystem.MinkowskiCounting D X (pendT X E hfin hst hLT pos F) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  exact invariance_representatives X E.toCEmb hfin hst (beLT hLT) D (thFOf X pos F) (delEquivOn_GdC X ℂ_[p]) (vtIn_GdC X ℂ_[p])

theorem invariance_of_trivial_stabilisers (D : Formalism.BasicNotions.D7) (hT : ∀ j c, (X.Lv.lev j c).TrivStab) :
    Formalism.MainNotions.FormalGroupSystem.MinkowskiCounting D X (pendT X E hfin hst hLT pos F) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  exact invariance_representatives_trivial X E.toCEmb hfin hst (beLT hLT) D (thFOf X pos F) hT (delEquivOn_GdC X ℂ_[p]) (vtIn_GdC X ℂ_[p])

theorem invariance_iff_additive_maps_exist (D : Formalism.BasicNotions.D7) :
    Formalism.MainNotions.FormalGroupSystem.adm5 D X (pendT X E hfin hst hLT pos F) ↔
      ∀ v, ∀ j < X.mm, letI := algKfC E.toCEmb; XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j :=
  condition_iff_additive_maps X E.toCEmb hfin hst (beLT hLT) _ _ _ D

end Formalism.L2.G.Pend
