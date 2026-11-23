import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OneMemZpowZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HTAaLbMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

section Inv

variable (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0)
  (hd : ∀ a, X0 a a = 1)

include hup hd

theorem det_one : X0.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]
  simp [hd]

theorem inv_mul : X0⁻¹ * X0 = 1 := Matrix.nonsing_inv_mul _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem mul_inv : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem inv_up : ∀ b a : Fin D.R.rS, a < b → X0⁻¹ b a = 0 := by
  have hU : IsUnit X0.det := by rw [det_one X0 hup hd]; exact isUnit_one
  have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
  haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
  exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h

theorem inv_diag : ∀ a, X0⁻¹ a a = 1 := by
  intro a
  have h := congrFun (congrFun (mul_inv X0 hup hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
  have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
    · rw [hup a e h1, zero_mul]
    · rw [inv_up X0 hup hd e a h1, mul_zero]
  rw [hz, add_zero] at h
  exact h

theorem map_inv' {K : Type*} [Field K] (f : D.host.E →+* K) : (X0.map f)⁻¹ = X0⁻¹.map f := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, inv_mul X0 hup hd, Matrix.map_one _ f.map_zero f.map_one]

end Inv

theorem gram_mem (xs : Fin D.R.rS → (VS D).V) (hxs : ∀ b, xs b ∈ aaLb X b) (b c : Fin D.R.rS) :
    Gq D xs b c ∈ aaD D b * aaD D c := by
  show (VS D).hT (xs b) (xs c) ∈ aaD D b * aaD D c
  suffices H : ∀ y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ d ∈ (aaD D c : Set D.host.E), ∃ l ∈ X.Lb, y = d • l},
      (VS D).hT (xs b) y ∈ aaD D b * aaD D c from H _ (hxs c)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, hdm, l, hl, rfl⟩ := hz
    rw [map_smul, smul_eq_mul, mul_comm d]
    exact FractionalIdeal.mul_mem_mul (LatA.hT_aaLb_mem X (hxs b) hl) hdm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [← algebraMap_smul D.host.E o x, map_smul, smul_eq_mul]
    exact LatA.fi_smul_mem hx o

end Formalism.L2.SG.Pf.NcReal.JX.NOf
