import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix

noncomputable section

def entrySum {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ := ∑ j, ∑ k, |A j k|

theorem entrySum_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : 0 ≤ entrySum A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem dot_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem mul_self_le_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) (j : ι) : x j * x j ≤ x ⬝ᵥ x :=
  Finset.single_le_sum (f := fun i => x i * x i) (fun i _ => mul_self_nonneg (x i))
    (Finset.mem_univ j)

theorem abs_mul_le_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) (j k : ι) :
    |x j| * |x k| ≤ x ⬝ᵥ x := by
  have hj := mul_self_le_dot x j
  have hk := mul_self_le_dot x k
  nlinarith [abs_mul_abs_self (x j), abs_mul_abs_self (x k), sq_nonneg (|x j| - |x k|)]

theorem abs_quad_le {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ entrySum A * (x ⬝ᵥ x) := by
  have h : x ⬝ᵥ (A *ᵥ x) = ∑ j, ∑ k, x j * A j k * x k := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h, entrySum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  calc |x j| * |A j k| * |x k| = |A j k| * (|x j| * |x k|) := by ring
    _ ≤ |A j k| * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left (abs_mul_le_dot x j k) (abs_nonneg _)

theorem quad_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((∑ j ∈ s, A j) *ᵥ x) = ∑ j ∈ s, x ⬝ᵥ (A j *ᵥ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, dotProduct_add, ih]

theorem quad_smul_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((l • (1 : Matrix ι ι ℝ) - A) *ᵥ x) = l * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem quad_sub_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((A - l • (1 : Matrix ι ι ℝ)) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - l * (x ⬝ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem posSemidef_of_real {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A)
    (h : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg
    ((conjTranspose_eq_transpose_of_trivial A).trans hs) (by simpa using h)

theorem quad_nonneg {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

theorem transpose_of_posSemidef {ι : Type*} {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : Aᵀ = A :=
  (conjTranspose_eq_transpose_of_trivial A).symm.trans hA.isHermitian

theorem quad_symm {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hs]

theorem quad_cs {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (u v : ι → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
  have hvu := quad_symm (transpose_of_posSemidef hA) u v
  have key : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ (A *ᵥ v)) * (t * t) + (2 * (u ⬝ᵥ (A *ᵥ v))) * t +
      u ⬝ᵥ (A *ᵥ u) := by
    intro t
    have h := quad_nonneg hA (u + t • v)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hvu] at h
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem posDef_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by
  have hs : Aᵀ = A := by
    have := transpose_of_posSemidef h
    rw [transpose_sub, transpose_smul, transpose_one] at this
    exact sub_left_injective this
  refine posDef_iff_dotProduct_mulVec.mpr ⟨(conjTranspose_eq_transpose_of_trivial A).trans hs,
    fun x hx => ?_⟩
  have h1 := quad_nonneg h x
  rw [quad_sub_smul_one] at h1
  have h2 : 0 < x ⬝ᵥ x := by
    rcases (dot_self_nonneg x).lt_or_eq with h3 | h3
    · exact h3
    · exact absurd (dotProduct_self_eq_zero.mp h3.symm) hx
  simpa using (by nlinarith : 0 < x ⬝ᵥ (A *ᵥ x))

theorem inv_le_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (c⁻¹ • (1 : Matrix ι ι ℝ) - A⁻¹).PosSemidef := by
  have hA : A.PosDef := posDef_of_ge hc h
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_smul_one_sub]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have h1 : c * (y ⬝ᵥ y) ≤ x ⬝ᵥ y := by
      have := quad_nonneg h y
      rw [quad_sub_smul_one, hx, dotProduct_comm] at this
      linarith
    have h3 : 0 ≤ (x - c • y) ⬝ᵥ (x - c • y) := dot_self_nonneg _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y x] at h3
    have key : c * (x ⬝ᵥ y) ≤ x ⬝ᵥ x := by nlinarith
    have := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
    linarith

theorem inv_ge_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {l : ℝ}
    (hl : 0 < l) (hA : A.PosDef) (h : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    (A⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_sub_smul_one]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hcs := quad_cs hA.posSemidef y x
    have e1 : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ x := by rw [← quad_symm hs, hx]
    have e2 : y ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by rw [hx, dotProduct_comm]
    rw [e1, e2] at hcs
    have hxy : 0 ≤ x ⬝ᵥ y := e2 ▸ quad_nonneg hA.posSemidef y
    have hlx : x ⬝ᵥ (A *ᵥ x) ≤ l * (x ⬝ᵥ x) := by
      have := quad_nonneg h x
      rw [quad_smul_one_sub] at this
      linarith
    have hxx := dot_self_nonneg x
    rcases hxx.lt_or_eq with hpos | hzero
    · have h4 : (x ⬝ᵥ x) * (x ⬝ᵥ x) ≤ (l * (x ⬝ᵥ y)) * (x ⬝ᵥ x) := by
        nlinarith [mul_le_mul_of_nonneg_left hlx hxy]
      have h5 : x ⬝ᵥ x ≤ l * (x ⬝ᵥ y) := le_of_mul_le_mul_right h4 hpos
      have := mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hl.le)
      rw [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] at this
      linarith
    · rw [← hzero]; simpa using hxy

open scoped ComplexOrder in

theorem posSemidef_map_ofReal {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A.map (fun x : ℝ => (x : ℂ))).PosSemidef := by
  have hs : ∀ j k, A k j = A j k := fun j k => by
    simpa using congrFun (congrFun (transpose_of_posSemidef hA) j) k
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext j k
    simp [conjTranspose_apply, hs]
  · set a : ι → ℝ := fun k => (w k).re
    set b : ι → ℝ := fun k => (w k).im
    have ha := quad_nonneg hA a
    have hb := quad_nonneg hA b
    have hre : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).re =
        a ⬝ᵥ (A *ᵥ a) + b ⬝ᵥ (A *ᵥ b) := by
      simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.re_sum, Complex.mul_re,
        Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, a, b, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have him : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im = 0 := by
      have e : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im =
          ∑ j, ∑ k, (w j).re * (A j k * (w k).im) - ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.mul_im, Complex.mul_re,
          Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.im_sum, Complex.ofReal_re,
          Complex.ofReal_im, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      have hsw : ∑ j, ∑ k, (w j).re * (A j k * (w k).im) =
          ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs]; ring
      rw [e, hsw, sub_self]
    exact Complex.nonneg_iff.mpr ⟨hre ▸ add_nonneg ha hb, him.symm⟩

end

end GroundTheory.Heights₂.Heights.MCBounds
