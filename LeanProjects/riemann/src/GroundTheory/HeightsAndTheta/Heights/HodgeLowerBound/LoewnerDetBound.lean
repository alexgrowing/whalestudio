import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem add_mul_eigenvalue_nonneg {M : Matrix n n ℂ} (hM : M.IsHermitian) {a b : ℝ}
    (h : ((a : ℂ) • (1 : Matrix n n ℂ) + (b : ℂ) • M).PosSemidef) (i : n) :
    0 ≤ a + b * hM.eigenvalues i := by
  set v : n → ℂ := ⇑(hM.eigenvectorBasis i) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := hM.eigenvectorBasis.orthonormal.ne_zero i
    apply h1
    ext j
    simpa [hv] using congrFun h0 j
  have hMv : M *ᵥ v = (hM.eigenvalues i : ℂ) • v := hM.mulVec_eigenvectorBasis i
  have h0 := h.dotProduct_mulVec_nonneg v
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hMv, smul_smul, ← add_smul,
    dotProduct_smul, smul_eq_mul] at h0
  have hs : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hv0
  have hx : ((a : ℂ) + (b : ℂ) * (hM.eigenvalues i : ℂ)) = ((a + b * hM.eigenvalues i : ℝ) : ℂ) := by
    push_cast; ring
  rw [hx] at h0
  have h2 := (Complex.nonneg_iff.mp h0).1
  rw [Complex.re_ofReal_mul] at h2
  exact (mul_nonneg_iff_of_pos_right (Complex.pos_iff.mp hs).1).mp h2

theorem norm_det_le_of_loewner {H A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : ((c : ℂ) • A - H).PosSemidef) (h₂ : ((c : ℂ) • A + H).PosSemidef) :
    0 ≤ A.det.re ∧ A.det.im = 0 ∧ ‖H.det‖ ≤ c ^ Fintype.card n * A.det.re := by
  have hA : A.PosSemidef := by
    have e : A = ((1 / (2 * c) : ℝ) : ℂ) • (((c : ℂ) • A + H) + ((c : ℂ) • A - H)) := by
      rw [show ((c : ℂ) • A + H) + ((c : ℂ) • A - H) = ((2 * c : ℝ) : ℂ) • A by
        push_cast; rw [mul_smul, two_smul]; abel, smul_smul, ← Complex.ofReal_mul,
        one_div_mul_cancel (by positivity), Complex.ofReal_one, one_smul]
    rw [e]
    exact (h₂.add h₁).smul (Complex.zero_le_real.mpr (by positivity))
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hA.det_nonneg
  refine ⟨hre, him.symm, ?_⟩
  by_cases h0 : A.det = 0
  · obtain ⟨v, hv0, hAv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have e1 : star v ⬝ᵥ (((c : ℂ) • A - H) *ᵥ v) = -(star v ⬝ᵥ (H *ᵥ v)) := by
      rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, dotProduct_neg]
    have e2 : star v ⬝ᵥ (((c : ℂ) • A + H) *ᵥ v) = star v ⬝ᵥ (H *ᵥ v) := by
      rw [add_mulVec, smul_mulVec, hAv, smul_zero, zero_add]
    have p1 := h₁.dotProduct_mulVec_nonneg v
    have p2 := h₂.dotProduct_mulVec_nonneg v
    rw [e1] at p1
    rw [e2] at p2
    have hz : star v ⬝ᵥ (H *ᵥ v) = 0 := le_antisymm (neg_nonneg.mp p1) p2
    have hw := (h₁.dotProduct_mulVec_zero_iff v).mp (by rw [e1, hz, neg_zero])
    rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, neg_eq_zero] at hw
    rw [exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hw⟩, norm_zero]
    exact mul_nonneg (pow_nonneg hc.le _) hre
  · obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    rw [star_eq_conjTranspose] at hL
    have hLu : IsUnit L.det := isUnit_iff_ne_zero.mpr fun hl => h0 (by rw [hL, det_mul, hl, mul_zero])
    have hLHu : IsUnit Lᴴ.det := by
      rw [det_conjTranspose]
      exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hLu))
    set M := (L⁻¹)ᴴ * H * L⁻¹ with hMdef
    have hHM : H = Lᴴ * M * L := by
      rw [hMdef, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu,
        Matrix.mul_one]
    have hA1 : (L⁻¹)ᴴ * A * L⁻¹ = 1 := by
      rw [hL, conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Lᴴ)⁻¹ Lᴴ L,
        Matrix.nonsing_inv_mul _ hLHu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hLu]
    have hconj : ∀ s : ℝ, (L⁻¹)ᴴ * ((c : ℂ) • A + (s : ℂ) • H) * L⁻¹ = (c : ℂ) • 1 + (s : ℂ) • M := by
      intro s
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        hA1, hMdef]
    have hP : ∀ s : ℝ, s = 1 ∨ s = -1 → ((c : ℂ) • (1 : Matrix n n ℂ) + (s : ℂ) • M).PosSemidef := by
      rintro s (rfl | rfl)
      · rw [← hconj]
        simpa using h₂.conjTranspose_mul_mul_same L⁻¹
      · rw [← hconj]
        have e : (c : ℂ) • A + ((-1 : ℝ) : ℂ) • H = (c : ℂ) • A - H := by
          push_cast; rw [neg_one_smul, ← sub_eq_add_neg]
        rw [e]
        exact h₁.conjTranspose_mul_mul_same L⁻¹
    have hM : M.IsHermitian := by
      have h3 := (hP 1 (Or.inl rfl)).isHermitian
      rw [IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one] at h3
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_one, map_one, one_smul] at h3
      exact add_left_cancel h3
    have hb : ∀ i, |hM.eigenvalues i| ≤ c := fun i => by
      have u := add_mul_eigenvalue_nonneg hM (hP 1 (Or.inl rfl)) i
      have l := add_mul_eigenvalue_nonneg hM (hP (-1) (Or.inr rfl)) i
      rw [abs_le]
      constructor <;> linarith
    have hdA : A.det = Lᴴ.det * L.det := by rw [hL, det_mul]
    have hnA : ‖A.det‖ = A.det.re := by
      rw [← Complex.re_add_im A.det, ← him]
      simp [Complex.norm_real, abs_of_nonneg hre]
    have hdH : ‖H.det‖ = ‖M.det‖ * ‖A.det‖ := by
      rw [hHM, det_mul, det_mul, hdA]
      simp only [norm_mul]
      ring
    have hdM : ‖M.det‖ ≤ c ^ Fintype.card n := by
      rw [hM.det_eq_prod_eigenvalues, norm_prod]
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_).trans_eq
        (by rw [Finset.prod_const, Finset.card_univ] : ∏ _i : n, c = c ^ Fintype.card n)
      have := hb i
      rwa [RCLike.norm_ofReal]
    rw [hdH, ← hnA]
    exact mul_le_mul_of_nonneg_right hdM (norm_nonneg _)

end GroundTheory.Heights₂.Heights.LowerBoundFree
