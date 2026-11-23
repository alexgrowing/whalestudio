import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB

variable {D : D7}

theorem hA_smul_left (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T (c • y) z = c * hA T y z := by
  simp only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hA_smul_right (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T y (c • z) = cA D c * hA T y z := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratV_smul' {n : ℕ} (c : D.host.E) (v : Fin n → D.host.E) : ratV (c • v) = incA D c • ratV v := by
  funext i; simp [ratV, map_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem xFB_col (F : Frames G) (hF : Std F) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) (p : Fin (σ + 1)) :
    (fun k => xFB F σ h' k p) = incA D ((-D.host.xi0) ^ (p.1 + 1)) •
      ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) := by
  obtain ⟨h2, he, -⟩ := hF.hB σ h'
  induction p using Fin.lastCases with
  | last =>
    have hc : (Fin.castLE (by omega) (Fin.last σ) : Fin (2 * σ + 2 - 1)) = ⟨σ, by omega⟩ := Fin.ext (by simp)
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_last, vecB, HypDec.j0, ← ratV_mulVec, Matrix.mulVec_mulVec,
      hF.ζ (σ + 1), Matrix.mulVec_smul, hF.zB' σ h', ratV_smul', Fin.val_last, hc]
  | cast i =>
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, rat, Matrix.map_apply, he, colsOf,
      Pi.smul_apply, smul_eq_mul, ratV, map_mul, Fin.coe_castSucc]
    rfl

theorem extY_col (F : Frames G) (hF : Std F) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)) :
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
        ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
          (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) =
      incA D (star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => a' k p := by
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hq := ProjTgt.qY_mul_a (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)) (F.dJ (σ + 1) h) (by omega) h2 he

  rw [HypDec.extY_apply, ← Matrix.mulVec_mulVec, HypDec.pY, ← ratV_mulVec]
  have hv : ∀ (M : Matrix (Fin (σ + 1)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) D.host.E)
      (N : Matrix (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (Fin (2 * (σ + 1) + 1 - 1)) D.host.E) (q : Fin (2 * (σ + 1) + 1 - 1)),
      M *ᵥ (fun k => N k q) = fun r => (M * N) r q := fun M N q => by
    funext r; simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hv, hq]
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ratV, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp only [if_true, mul_one]; ring
  · intro r _ hr
    have : ¬ ((Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev = (Fin.castLE (by omega) r).rev) := by
      intro e; apply hr; rw [Fin.rev_inj] at e; exact Fin.ext (by simpa [Fin.ext_iff] using e.symm)
    simp only [this, if_false, mul_zero, map_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem hA_xFB_col : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)),
    hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) =
      hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
          ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
            (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  intro D _ T L _ _ sc G _ _ _ F hF σ h h' a' p
  rw [xFB_col F hF σ h' p, extY_col F hF σ h a' p, hA_smul_left, hA_smul_right, GlobalTheory.DualPairCheck.cA_incA, star_star]

example (T : HSp D) (c : AE D) : hA T (c • 0) 0 = c * hA T 0 0 := hA_smul_left T c 0 0

end GlobalTheory.CharXFB
