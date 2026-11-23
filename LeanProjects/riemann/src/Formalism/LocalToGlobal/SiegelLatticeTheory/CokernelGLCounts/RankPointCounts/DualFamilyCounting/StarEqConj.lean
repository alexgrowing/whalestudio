import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GpHerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibT

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem star_eq_conj' (t : D.host.E) : star t = D.host.conj t := by
  apply D.host.φ₀.injective
  rw [Formalism.BasicNotions.Examples₂.emb_star, Formalism.BasicNotions.Examples₂.emb_conj]

theorem theta_spec : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dif_pos h]
  exact h.choose_spec

theorem entry_rel {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (b a : Fin D.R.rS) :
    M b a + star (M a b) = -Gp D X0 xs b a := by
  have hok' := hok
  obtain ⟨-, -, -, hM⟩ := hok'
  have h := congrFun (congrFun hM b) a
  simpa only [Matrix.add_apply, Matrix.neg_apply, Matrix.conjTranspose_apply] using h

theorem kblk {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (p : Formalism.L2.SG.Pf.LsNc5.LtPair D.R.rS) :
    blkQ X u X0 xs M (Sum.inr (Sum.inl p)) - tauQ X u (Sum.inr (Sum.inl p)) (blkQ X u X0 xs M) =
      embV X (M p.1.1 p.1.2) := by
  have hok' := hok
  obtain ⟨hup, hd, hW, -⟩ := hok'
  show (fun v => (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2) -
      (fun v => Hc X u (blkQ X u X0 xs M) v p.1.1 p.1.2 / 2) =
      fun v => embS D (X.pl v) (M p.1.1 p.1.2)
  funext v
  simp only [Pi.sub_apply]
  rw [Hc_blkQ X u X0 xs M hup hd hW v, Matrix.map_apply]
  have e := congrArg (embS D (X.pl v)) (entry_rel X hok p.1.1 p.1.2)
  rw [map_add, map_neg, Formalism.BasicNotions.Examples₂.emb_star, starRingEnd_apply] at e
  rw [show embS D (X.pl v) (Gp D X0 xs p.1.1 p.1.2) =
      -(embS D (X.pl v) (M p.1.1 p.1.2) + star (embS D (X.pl v) (M p.1.2 p.1.1))) by
    rw [e, neg_neg]]
  ring

def xiA (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (a : Fin D.R.rS) : D.host.E :=
  M a a + Gp D X0 xs a a * theta D

theorem Gp_diag_star (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) (a : Fin D.R.rS) :
    star (Gp D X0 xs a a) = Gp D X0 xs a a := by
  have h := congrFun (congrFun (Gp_herm X0 xs) a) a
  simpa only [Matrix.conjTranspose_apply] using h

theorem xiA_conj {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (a : Fin D.R.rS) :
    D.host.conj (xiA X0 xs M a) = -xiA X0 xs M a := by
  have hs : ∀ t : D.host.E, D.host.conj t = star t := fun t => (star_eq_conj' t).symm
  have hθ : D.host.conj (theta D) = 1 - theta D := eq_sub_of_add_eq' (theta_spec (D := D)).2
  have hM : star (M a a) = -Gp D X0 xs a a - M a a := eq_sub_of_add_eq' (entry_rel X hok a a)
  unfold xiA
  rw [map_add, map_mul, hθ, hs (M a a), hs (Gp D X0 xs a a), Gp_diag_star X0 xs a, hM]
  ring

theorem imblk {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (a : Fin D.R.rS) :
    blkQ X u X0 xs M (Sum.inr (Sum.inr a)) - tauQ X u (Sum.inr (Sum.inr a)) (blkQ X u X0 xs M) =
      fun v => (embS D (X.pl v) (xiA X0 xs M a)).im := by
  have hok' := hok
  obtain ⟨hup, hd, hW, -⟩ := hok'
  show (fun v => (embS D (X.pl v) (M a a)).im) -
      (fun v => -((Hc X u (blkQ X u X0 xs M) v a a).re * (embS D (X.pl v) (theta D)).im)) =
      fun v => (embS D (X.pl v) (xiA X0 xs M a)).im
  funext v
  simp only [Pi.sub_apply]
  rw [Hc_blkQ X u X0 xs M hup hd hW v, Matrix.map_apply]
  have hreal : (embS D (X.pl v) (Gp D X0 xs a a)).im = 0 := by
    have h1 := congrArg (embS D (X.pl v)) (Gp_diag_star X0 xs a)
    rw [Formalism.BasicNotions.Examples₂.emb_star] at h1
    exact Complex.conj_eq_iff_im.mp h1
  simp only [xiA, map_add, map_mul, Complex.add_im, Complex.mul_im, hreal]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
