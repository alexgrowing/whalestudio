import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.B

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem herm_apply (y : E n) (i j : Fin n) : herm y i j = ⟨(y i j + y j i) / 2, (y i j - y j i) / 2⟩ := by
  apply Complex.ext <;> simp [herm]

theorem herm_conjTranspose (y : E n) : (herm y)ᴴ = herm y := by
  ext i j
  rw [conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext <;> simp <;> ring

def Am (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 - (Complex.I * s) • herm y

def Bm (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 + (Complex.I * s) • herm y

theorem sq_of_pm {s : ℂ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem star_of_pm {s : ℂ} (hs : s = 1 ∨ s = -1) : star s = s := by
  rcases hs with rfl | rfl <;> simp

theorem Is_sq {s : ℂ} (hs : s = 1 ∨ s = -1) : (Complex.I * s) * (Complex.I * s) = -1 := by
  rw [mul_mul_mul_comm, Complex.I_mul_I, sq_of_pm hs]
  ring

theorem Am_conjTranspose {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y)ᴴ = Bm s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, sub_neg_eq_add]

theorem Bm_conjTranspose {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y)ᴴ = Am s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, ← sub_eq_add_neg]

theorem Bm_mul_Am {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : Bm s y * Am s y = 1 + herm y * herm y := by
  unfold Am Bm
  simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, Is_sq hs, neg_one_smul]
  abel

theorem Am_mul_Bm {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : Am s y * Bm s y = 1 + herm y * herm y := by
  unfold Am Bm
  simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, Is_sq hs, neg_one_smul]
  abel

theorem posDef_one_add (y : E n) : (1 + herm y * herm y).PosDef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (herm y)
  rw [herm_conjTranspose] at h
  exact Matrix.PosDef.one.add_posSemidef h

theorem det_one_add_eq (y : E n) : (1 + herm y * herm y).det = ((dP y : ℝ) : ℂ) := by
  have h := (posDef_one_add y).det_pos
  rw [Complex.lt_def] at h
  apply Complex.ext
  · simp [dP]
  · simp only [Complex.ofReal_im]
    simpa using h.2.symm

theorem dP_pos (y : E n) : 0 < dP y := by
  have h := (posDef_one_add y).det_pos
  rw [Complex.lt_def] at h
  simpa [dP] using h.1

theorem det_Bm_mul_det_Am {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) :
    (Bm s y).det * (Am s y).det = ((dP y : ℝ) : ℂ) := by
  rw [← det_mul, Bm_mul_Am hs, det_one_add_eq]

theorem det_Am_ne {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, mul_zero] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)

theorem det_Bm_ne {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, zero_mul] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)

theorem uM_eq (s : ℂ) (y : E n) : uM s y = (Am s y)⁻¹ := rfl

theorem vM_eq (s : ℂ) (y : E n) : vM s y = (Bm s y)⁻¹ := rfl

theorem star_dot_self (v : Fin n → ℂ) : (star v ⬝ᵥ v) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Complex.conj_mul' (v i)

theorem norm_sq_ge {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y) (x : Fin n → ℂ) :
    ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖(M *ᵥ x) i‖ ^ 2 := by
  have key : ((∑ i, ‖(M *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) =
      ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) + ((∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← star_dot_self (M *ᵥ x), ← star_dot_self x, ← star_dot_self (herm y *ᵥ x)]
    simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hM, herm_conjTranspose, add_mulVec, one_mulVec,
      dotProduct_add]
  have key' : ∑ i, ‖(M *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 + ∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 := by
    exact_mod_cast key
  rw [key']
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => by positivity)

theorem norm_entry_le {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y)
    (hd : M.det ≠ 0) (a b : Fin n) : ‖M⁻¹ a b‖ ≤ 1 := by
  have hMx : M *ᵥ (M⁻¹ *ᵥ Pi.single b 1) = Pi.single b 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hd), one_mulVec]
  have h1 := norm_sq_ge y hM (M⁻¹ *ᵥ Pi.single b 1)
  rw [hMx] at h1
  have hsum1 : ∑ i, ‖(Pi.single b (1 : ℂ) : Fin n → ℂ) i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have hxa : (M⁻¹ *ᵥ Pi.single b 1) a = M⁻¹ a b := by
    simp [mulVec, dotProduct, Pi.single_apply]
  have h2 : ‖M⁻¹ a b‖ ^ 2 ≤ 1 := by
    rw [← hxa, ← hsum1]
    refine le_trans ?_ h1
    exact Finset.single_le_sum (f := fun i => ‖(M⁻¹ *ᵥ Pi.single b 1) i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ a)
  nlinarith [norm_nonneg (M⁻¹ a b)]

theorem norm_uM_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖uM s y a b‖ ≤ 1 := by
  rw [uM_eq]
  exact norm_entry_le y (by rw [Am_conjTranspose hs, Bm_mul_Am hs]) (det_Am_ne hs y) a b

theorem norm_vM_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖vM s y a b‖ ≤ 1 := by
  rw [vM_eq]
  exact norm_entry_le y (by rw [Bm_conjTranspose hs, Am_mul_Bm hs]) (det_Bm_ne hs y) a b

theorem norm_det_Am_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Am s y).det‖ ^ 2 = dP y := by
  have h := det_Bm_mul_det_Am hs y
  rw [← Am_conjTranspose hs, det_conjTranspose] at h
  have h2 : star (Am s y).det * (Am s y).det = ((‖(Am s y).det‖ : ℂ)) ^ 2 := Complex.conj_mul' _
  rw [h2] at h
  exact_mod_cast h

theorem norm_det_Bm_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Bm s y).det‖ ^ 2 = dP y := by
  have h := det_Bm_mul_det_Am hs y
  rw [← Bm_conjTranspose hs, det_conjTranspose, mul_comm] at h
  have h2 : star (Bm s y).det * (Bm s y).det = ((‖(Bm s y).det‖ : ℂ)) ^ 2 := Complex.conj_mul' _
  rw [h2] at h
  exact_mod_cast h

theorem norm_det_uM_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(uM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [uM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Am_sq hs]

theorem norm_det_vM_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(vM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [vM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Bm_sq hs]

theorem norm_det_pow {x : ℂ} {d : ℝ} (hd : 0 < d) (h : ‖x‖ ^ 2 = d⁻¹) (p : ℕ) : ‖x ^ p‖ = d ^ (-(p : ℝ) / 2) := by
  have h1 : (d ^ (-(1 : ℝ) / 2)) ^ 2 = d⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
    exact Real.rpow_neg_one d
  have h2 : 0 ≤ d ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hd.le _
  have hx : ‖x‖ = d ^ (-(1 : ℝ) / 2) := (pow_left_inj₀ (norm_nonneg _) h2 two_ne_zero).mp (h.trans h1.symm)
  rw [norm_pow, hx, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  congr 1
  ring

end PositivityTheory.Rg.Sw.WR.B
