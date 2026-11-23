import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopConstantTwist
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PTelescope
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace TopConstantTwistAlt

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem cxHessian_add_const (f : (Fin e → ℂ) → ℝ) (C : ℝ) (y : Fin e → ℂ) :
    cxHessian (fun y' => f y' + C) y = cxHessian f y := by
  have h : fderiv ℝ (fun y' => f y' + C) = fderiv ℝ f := funext fun _ => fderiv_add_const _
  unfold cxHessian
  rw [h]

theorem ptsIntegral_congr_add_const (P : Ideal (MRing ι)) (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (C : Fin e → ℝ) (h : ∀ j z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → φ j z = φ' j z + C j)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral P φ g = ptsIntegral P φ' g := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      unfold maDensity
      congr 3
      funext j
      have hev : (fun y' => φ j (hγ.choose y')) =ᶠ[𝓝 y] (fun y' => φ' j (hγ.choose y') + C j) := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact h j _ hy'.2.1.1
      rw [cxHessian_congr hev, cxHessian_add_const]
    · rfl
  · rfl

theorem ptsIntegral_const_weight (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_congr fun w => ?_
    congr 1
    funext _
    unfold sheetDensity
    split_ifs <;> ring
  · ring

theorem ptsIntegral_twist_term (P : Ideal (MRing ι)) (A : HermLine ι) (c : ℝ) (D i : ℕ) :
    ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) =
      c * geomDeg P A D := by
  rw [ptsIntegral_const_weight, geomDeg]
  congr 1
  refine ptsIntegral_congr_add_const P _ _ (fun j => if (j : ℕ) < i then -c else 0) (fun j z hz => ?_) _
  unfold pot
  dsimp only
  split_ifs
  · show Real.log (A.h z * Real.exp (-c)) = Real.log (A.h z) + -c
    rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]
  · simp

end TopConstantTwistAlt

open TopConstantTwistAlt in

theorem TopConstantTwist.proof : TopConstantTwist.Statement := by
  intro K _ ι _ P D A c II hII hP hA
  have h : II K ι P (D + 1) (fun _ => A.tensor (constLine c)) - II K ι P (D + 1) (fun _ => A) =
      -∑ i ∈ Finset.range (D + 1),
        ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) :=
    GroundTheory.Heights₂.Heights.Telescope.proof K ι (II K ι) (hII K ι) P D A (fun _ => c) (fun _ _ _ => rfl) hP hA
      contDiffOn_const
  simp only [ptsIntegral_twist_term, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h ⊢
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
