import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartMongeAmpereAffineInvariance

variable {e : ℕ}

theorem mulVec_cons_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (y : Fin e → ℂ) :
    T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) =
      Fin.cons (T 0 0) ((fun i => T i.succ 0) + (T.submatrix Fin.succ Fin.succ) *ᵥ y) := by
  funext p
  refine Fin.cases ?_ (fun i => ?_) p
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, hT]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ]

theorem det_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0) :
    T.det = T 0 0 * (T.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [hT, Fin.succAbove_zero]

theorem hermChartPot_conj (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (ht : T 0 0 ≠ 0) (y : Fin e → ℂ) :
    hermChartPot (Tᴴ * M * T) y =
      hermChartPot M ((T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) +
        Real.log ‖T 0 0‖ := by
  set w : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y with hw
  set u : Fin (e + 1) → ℂ := Fin.cons 1 w with hu
  have hTv : T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) = T 0 0 • u := by
    rw [mulVec_cons_of_row_zero T hT]
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp [u]
    · have hm : (((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) i =
          (T 0 0)⁻¹ * ((T.submatrix Fin.succ Fin.succ) *ᵥ y) i := by
        simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      simp only [u, w, Fin.cons_succ, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hm]
      field_simp
  have hq : star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Tᴴ * M * T) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (Complex.normSq (T 0 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (T 0 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr ht) (Real.sqrt_pos.mpr hx).ne']
  ring

theorem chartMass_conj (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (hdet : T.det ≠ 0) :
    chartMass (Tᴴ * M * T) = chartMass M := by
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set C := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hCdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hC' : C.det ≠ 0 := by
    rw [hCdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfun : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + C *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  unfold chartMass
  rw [hfun]
  simp_rw [maDensity_comp_affine (hermChartPot M) c C hC']
  rw [integral_const_mul, integral_comp_affine (maDensity fun _ => hermChartPot M) c C hC', ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hC').ne', one_mul]

end ChartMongeAmpereAffineInvariance

open ChartMongeAmpereAffineInvariance in

theorem ChartMassInvariant.proof : ChartMassInvariant.Statement := by
  intro e M hM
  let S : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := M
  have hS : S.PosDef := hM
  let P₀ : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := LDL.lowerInv hS
  let P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := P₀
  have hPdet : P.det ≠ 0 := (isUnit_det_of_invertible P₀).ne_zero
  set T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Pᴴ with hTdef
  have hT : ∀ j : Fin e, T 0 j.succ = 0 := fun j => by
    have h := LDL.lowerInv_triangular hS (i := OrderDual.toDual j.succ) (j := OrderDual.toDual 0)
      (OrderDual.toDual_lt_toDual.mpr (Fin.succ_pos j))
    rw [hTdef, conjTranspose_apply, show P j.succ 0 = 0 from h, star_zero]
  have hTdet : T.det ≠ 0 := by
    rw [hTdef, det_conjTranspose]
    exact star_ne_zero.mpr hPdet
  let d₀ : (Fin (e + 1))ᵒᵈ → ℂ := LDL.diagEntries hS
  set d : Fin (e + 1) → ℂ := d₀ with hddef
  have hD : Tᴴ * M * T = diagonal d := by
    rw [hTdef, conjTranspose_conjTranspose]
    exact (LDL.diag_eq_lowerInv_conj hS).symm
  have hDpos : (diagonal d).PosDef := by
    rw [← hD]
    exact hM.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hTdet)))
  have hdpos : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  set T' : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := diagonal fun i => ((Real.sqrt (d i).re)⁻¹ : ℝ) with hT'def
  have hT' : ∀ j : Fin e, T' 0 j.succ = 0 := fun j => diagonal_apply_ne _ (Fin.succ_ne_zero j).symm
  have hT'det : T'.det ≠ 0 := by
    rw [hT'def, det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (Complex.pos_iff.mp (hdpos i)).1).ne')
  have h1 : T'ᴴ * diagonal d * T' = 1 := by
    rw [hT'def, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    obtain ⟨hr, him⟩ := Complex.pos_iff.mp (hdpos i)
    set r := (d i).re with hrdef
    have hdi : d i = (r : ℂ) := Complex.ext (by simp [hrdef]) (by simp [← him])
    have key : (Real.sqrt r)⁻¹ * r * (Real.sqrt r)⁻¹ = 1 := by
      have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
      rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hr.le, inv_mul_cancel₀ hr.ne']
    rw [hdi, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast key
  calc chartMass M = chartMass (Tᴴ * M * T) := (chartMass_conj M T hM hT hTdet).symm
    _ = chartMass (diagonal d) := by rw [hD]
    _ = chartMass (T'ᴴ * diagonal d * T') := (chartMass_conj _ T' hDpos hT' hT'det).symm
    _ = chartMass 1 := by rw [h1]

end

end GroundTheory.Heights₂.Heights
