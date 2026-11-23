import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PWOfInW

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem h_sum_left (a : Fin D.R.rS → D.host.E) (x : Fin D.R.rS → (VS D).V) (y : (VS D).V) :
    (VS D).hT (∑ c, a c • x c) y = ∑ c, star (a c) * (VS D).hT (x c) y := by
  simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, starRingEnd_apply]

theorem h_sum_right (a : Fin D.R.rS → D.host.E) (x : Fin D.R.rS → (VS D).V) (y : (VS D).V) :
    (VS D).hT y (∑ c, a c • x c) = ∑ c, a c * (VS D).hT y (x c) := by
  simp [map_sum, map_smul]

theorem h_e_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) : (VS D).hT (X.eX c) (nF X X0 xs M b) = Ym X0 c b := by
  unfold nF om
  rw [map_add, map_add, map_neg, h_sum_right, h_sum_right, h_sum_right]
  have hx1 : ∀ c d, (VS D).hT (X.eX c) (xs d) = 0 := fun c d => (hxs d c).1
  simp [X.ef, X.ee, hx1, Finset.sum_ite_eq]

theorem h_f_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) : (VS D).hT (X.fY c) (nF X X0 xs M b) = (X0 * M) c b := by
  unfold nF om
  rw [map_add, map_add, map_neg, h_sum_right, h_sum_right, h_sum_right]
  have hx2 : ∀ c d, (VS D).hT (X.fY c) (xs d) = 0 := fun c d => (hxs d c).2
  simp [X.ff, h_fe, hx2, Finset.sum_ite_eq]

theorem h_xs_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) :
    (VS D).hT (xs c) (nF X X0 xs M b) = -∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) := by
  unfold nF om
  rw [map_add, map_add, map_neg, h_sum_right, h_sum_right, h_sum_right]
  simp [(inW_left X (hxs c) _).1, (inW_left X (hxs c) _).2]

theorem h_nF_left (a : Fin D.R.rS) (y : (VS D).V) :
    (VS D).hT (nF X X0 xs M a) y = ∑ c, star (Ym X0 c a) * (VS D).hT (X.fY c) y -
      ∑ c, star (Ym X0 c a) * (VS D).hT (xs c) y + ∑ c, star ((X0 * M) c a) * (VS D).hT (X.eX c) y := by
  unfold nF om
  rw [LinearMap.map_add₂, LinearMap.map_add₂, LinearMap.map_neg₂, h_sum_left, h_sum_left, h_sum_left]
  ring

theorem h_nE_left (a : Fin D.R.rS) (y : (VS D).V) :
    (VS D).hT (nE X X0 a) y = ∑ c, star (X0 c a) * (VS D).hT (X.eX c) y := by
  unfold nE
  rw [h_sum_left]

theorem g_ee (a b : Fin D.R.rS) : (VS D).hT (nE X X0 a) (nE X X0 b) = (VS D).hT (X.eX a) (X.eX b) := by
  rw [h_nE_left, X.ee]
  unfold nE
  simp [h_sum_right, X.ee]

theorem g_ef (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (a b : Fin D.R.rS) :
    (VS D).hT (nE X X0 a) (nF X X0 xs M b) = (VS D).hT (X.eX a) (X.fY b) := by
  rw [h_nE_left, X.ef]
  simp_rw [h_e_nF X X0 xs M hxs]
  have h1 : (X0ᴴ * Ym X0) a b = ∑ c, star (X0 c a) * Ym X0 c b := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h2 : X0ᴴ * Ym X0 = 1 := by
    unfold Ym
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  rw [← h1, h2, Matrix.one_apply]

theorem g_ff (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) (a b : Fin D.R.rS) :
    (VS D).hT (nF X X0 xs M a) (nF X X0 xs M b) = (VS D).hT (X.fY a) (X.fY b) := by
  rw [h_nF_left, X.ff]
  simp_rw [h_f_nF X X0 xs M hxs, h_xs_nF X X0 xs M hxs, h_e_nF X X0 xs M hxs]
  have hY : (Ym X0)ᴴ = X0⁻¹ := by unfold Ym; rw [Matrix.conjTranspose_conjTranspose]
  have e1 : ∑ c, star (Ym X0 c a) * (X0 * M) c b = M a b := by
    have : ((Ym X0)ᴴ * (X0 * M)) a b = ∑ c, star (Ym X0 c a) * (X0 * M) c b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← this, hY, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have e2 : ∑ c, star ((X0 * M) c a) * Ym X0 c b = Mᴴ a b := by
    have : ((X0 * M)ᴴ * Ym X0) a b = ∑ c, star ((X0 * M) c a) * Ym X0 c b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← this, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    unfold Ym
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one, Matrix.mul_one]
  have e3 : ∑ c, star (Ym X0 c a) * -∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) = -(Gp D X0 xs) a b := by
    have : ((Ym X0)ᴴ * Gq D xs * Ym X0) a b = ∑ c, star (Ym X0 c a) * ∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Gq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [← this, hY]
    rfl
  rw [e1, e3, e2]
  have := congrFun (congrFun hM a) b
  simp only [Matrix.add_apply, Matrix.neg_apply] at this
  rw [sub_neg_eq_add]
  linear_combination this

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
