import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegularPosCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBound
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.IsomBound

open GlobalTheory.SgInf.FrameBound

variable {n : ℕ} {ι : Type} [Fintype ι]

theorem eucl_add_le (u v : Fin n → ℂ) : eucl (u + v) ≤ eucl u + eucl v := by
  rw [eucl_eq, eucl_eq, eucl_eq]
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)

theorem eucl_sub_le (u v : Fin n → ℂ) : eucl (u - v) ≤ eucl u + eucl v := by
  rw [eucl_eq, eucl_eq, eucl_eq]
  exact norm_sub_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)

theorem eucl_smul (c : ℂ) (v : Fin n → ℂ) : eucl (c • v) = ‖c‖ * eucl v := by
  rw [eucl_eq, eucl_eq]
  exact norm_smul c (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))

theorem eucl_sum_le {κ : Type} (s : Finset κ) (f : κ → Fin n → ℂ) :
    eucl (∑ i ∈ s, f i) ≤ ∑ i ∈ s, eucl (f i) := by
  simp only [eucl_eq]
  rw [WithLp.toLp_sum]
  exact norm_sum_le _ _

theorem norm_star_dot_le (w v : Fin n → ℂ) : ‖star w ⬝ᵥ v‖ ≤ eucl w * eucl v := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← eucl_eq, ← eucl_eq] at h
  exact h

theorem star_dot_self (v : Fin n → ℂ) : star v ⬝ᵥ v = ((eucl v ^ 2 : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← eucl_eq] at h
  rw [h]; norm_cast

theorem star_dot_mulVec (H : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) :
    star (H *ᵥ w) ⬝ᵥ v = star w ⬝ᵥ (Hᴴ *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec]

theorem eucl_mulVec_of_unitary {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * H = 1) (v : Fin n → ℂ) :
    eucl (H *ᵥ v) = eucl v := by
  have h1 := star_dot_self (H *ᵥ v)
  rw [star_dot_mulVec, mulVec_mulVec, hH, one_mulVec, star_dot_self] at h1
  have h2 : eucl (H *ᵥ v) ^ 2 = eucl v ^ 2 := by exact_mod_cast h1.symm
  exact (pow_left_inj₀ (eucl_nonneg _) (eucl_nonneg _) two_ne_zero).1 h2

def fam (b : ι → Fin n → ℂ) : Matrix (Fin n) ι ℂ := fun p i => b i p

theorem fam_mulVec (b : ι → Fin n → ℂ) (x : ι → ℂ) : fam b *ᵥ x = ∑ i, x i • b i := by
  funext p
  simp [fam, mulVec, dotProduct, Finset.sum_apply, mul_comm]

omit [Fintype ι] in
theorem famH_mulVec_apply (b : ι → Fin n → ℂ) (y : Fin n → ℂ) (j : ι) :
    ((fam b)ᴴ *ᵥ y) j = star (b j) ⬝ᵥ y := by
  simp [fam, mulVec, dotProduct, conjTranspose_apply]

omit [Fintype ι] in
theorem mul_fam (s : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) :
    s * fam b = fam (fun i => s *ᵥ b i) := by
  ext p i
  simp [fam, mul_apply, mulVec, dotProduct]

omit [Fintype ι] in
theorem famH_mul_mul_fam (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) (m i : ι) :
    ((fam b)ᴴ * H * fam b) m i = herm H (b i) (b m) := by
  simp only [herm, Matrix.mul_apply, fam, mulVec, dotProduct, conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.star_apply]; ring

theorem eucl_fam_mulVec_le (b : ι → Fin n → ℂ) (M : ℝ) (hM : ∀ i, eucl (b i) ≤ M) (x : ι → ℂ) :
    eucl (fam b *ᵥ x) ≤ M * ∑ i, ‖x i‖ := by
  rw [fam_mulVec]
  refine (eucl_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [eucl_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)

theorem sum_norm_mulVec_le (Ti : Matrix ι ι ℂ) (y : ι → ℂ) (Y : ℝ) (hY : ∀ j, ‖y j‖ ≤ Y) :
    ∑ i, ‖(Ti *ᵥ y) i‖ ≤ (∑ i, ∑ j, ‖Ti i j‖) * Y := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hY j) (norm_nonneg _)

omit [Fintype ι] in
theorem vecMul_fam (c : ι → Fin n → ℂ) (y : Fin n → ℂ) (i : ι) : (y ᵥ* fam c) i = y ⬝ᵥ c i := by
  simp [fam, vecMul, dotProduct]

theorem herm_fam_mulVec (H : Matrix (Fin n) (Fin n) ℂ) (c : ι → Fin n → ℂ) (x : ι → ℂ) (v : Fin n → ℂ) :
    herm H (fam c *ᵥ x) v = ∑ i, herm H (c i) v * x i := by
  unfold herm
  rw [mulVec_mulVec, dotProduct_mulVec, mul_fam]
  simp only [dotProduct, vecMul_fam]

theorem herm_swap {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (v w : Fin n → ℂ) :
    herm H v w = star (herm H w v) := by
  unfold herm
  rw [star_dotProduct, star_dot_mulVec, hH]

theorem herm_sub_smul {H : Matrix (Fin n) (Fin n) ℂ} (v w : Fin n → ℂ) (t : ℂ) :
    herm H (v - t • w) (v - t • w) =
      herm H v v - t * herm H w v - star t * herm H v w + star t * t * herm H w w := by
  simp only [herm, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, star_sub, star_smul,
    sub_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

theorem herm_re_le {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * H = 1) (w : Fin n → ℂ) :
    (herm H w w).re ≤ eucl w ^ 2 := by
  refine (Complex.re_le_norm _).trans ?_
  unfold herm
  refine (norm_star_dot_le _ _).trans ?_
  rw [eucl_mulVec_of_unitary hH, sq]

def gram (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) : Matrix ι ι ℂ := fun m i => herm H (b i) (b m)

omit [Fintype ι] in
theorem gram_eq (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) : gram H b = (fam b)ᴴ * H * fam b := by
  ext m i; rw [famH_mul_mul_fam]; rfl

theorem eucl_proj_le {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * H = 1) (b b' : ι → Fin n → ℂ)
    (Ti : Matrix ι ι ℂ) (M M' : ℝ) (hM' : 0 ≤ M') (hM : ∀ i, eucl (b i) ≤ M) (hb' : ∀ i, eucl (b' i) ≤ M')
    (u : Fin n → ℂ) :
    eucl (fam b' *ᵥ (Ti *ᵥ ((fam b)ᴴ *ᵥ (H *ᵥ u)))) ≤ M' * ((∑ i, ∑ j, ‖Ti i j‖) * (M * eucl u)) := by
  refine (eucl_fam_mulVec_le b' M' hb' _).trans (mul_le_mul_of_nonneg_left ?_ hM')
  refine sum_norm_mulVec_le Ti _ _ fun j => ?_
  rw [famH_mulVec_apply]
  refine (norm_star_dot_le _ _).trans ?_
  rw [eucl_mulVec_of_unitary hH]
  exact mul_le_mul_of_nonneg_right (hM j) (eucl_nonneg _)

omit [Fintype ι] in

theorem sq_le_of_pos {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (b' : ι → Fin n → ℂ) (hpos : ∀ y, (∀ i, herm H y (b' i) = 0) → 0 ≤ (herm H y y).re)
    (v w : Fin n → ℂ) (hv : ∀ i, herm H v (b' i) = 0) (hw : ∀ i, herm H w (b' i) = 0)
    (hwv : herm H w v = ((eucl v ^ 2 : ℝ) : ℂ)) (a : ℝ) (ha : 0 < a) (hw2 : eucl w ≤ a * eucl v) :
    eucl v ^ 2 ≤ a ^ 2 * (herm H v v).re := by
  have hH' : Hᴴ * H = 1 := by rw [hH, hH2]
  set t : ℝ := 1 / a ^ 2 with ht
  have hy : ∀ i, herm H (v - (t : ℂ) • w) (b' i) = 0 := fun i => by
    simp only [herm, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change herm H v (b' i) - _ * herm H w (b' i) = 0
    rw [hv, hw, mul_zero, sub_zero]
  have h0 := hpos _ hy
  rw [herm_sub_smul, herm_swap hH v w, hwv] at h0
  have hW := herm_re_le hH' w
  have ht0 : 0 < t := by positivity
  have hwa : eucl w ^ 2 ≤ a ^ 2 * eucl v ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (eucl_nonneg _) hw2 2
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_ofReal, mul_assoc,
    Complex.re_ofReal_mul, Complex.ofReal_re] at h0
  have hta : t * a ^ 2 = 1 := by rw [ht]; field_simp
  have h1 : t * (t * (herm H w w).re) ≤ t * eucl v ^ 2 := by
    calc t * (t * (herm H w w).re) ≤ t * (t * (a ^ 2 * eucl v ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hW.trans hwa) ht0.le) ht0.le
      _ = t * eucl v ^ 2 := by rw [← mul_assoc t (a ^ 2), hta, one_mul]
  have h2 : t * eucl v ^ 2 ≤ (herm H v v).re := by linarith
  calc eucl v ^ 2 = a ^ 2 * (t * eucl v ^ 2) := by rw [← mul_assoc, mul_comm (a ^ 2) t, hta, one_mul]
    _ ≤ a ^ 2 * (herm H v v).re := mul_le_mul_of_nonneg_left h2 (sq_nonneg a)

variable [DecidableEq ι]

def proj (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) (Ti : Matrix ι ι ℂ) (u : Fin n → ℂ) :
    Fin n → ℂ :=
  fam b *ᵥ (Ti *ᵥ ((fam b)ᴴ *ᵥ (H *ᵥ u)))

theorem herm_sub_proj {H : Matrix (Fin n) (Fin n) ℂ} {b : ι → Fin n → ℂ} {Ti : Matrix ι ι ℂ}
    (hTi : gram H b * Ti = 1) (u : Fin n → ℂ) (m : ι) : herm H (u - proj H b Ti u) (b m) = 0 := by
  have e : ∀ x : Fin n → ℂ, herm H x (b m) = ((fam b)ᴴ *ᵥ (H *ᵥ x)) m := fun x => by
    rw [famH_mulVec_apply]; rfl
  rw [e, proj]
  simp only [mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc]
  rw [← gram_eq, hTi, Matrix.one_mul, sub_self, Pi.zero_apply]

theorem sq_le_compl {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (b' : ι → Fin n → ℂ) (Ti : Matrix ι ι ℂ) (hTi : gram H b' * Ti = 1)
    (hpos : ∀ y, (∀ i, herm H y (b' i) = 0) → 0 ≤ (herm H y y).re)
    (β : ℝ) (hβ : 0 ≤ β) (hb' : ∀ i, eucl (b' i) ≤ β) (v : Fin n → ℂ) (hv : ∀ i, herm H v (b' i) = 0) :
    eucl v ^ 2 ≤ (1 + (∑ i, ∑ j, ‖Ti i j‖) * β ^ 2) ^ 2 * (herm H v v).re := by
  have hH' : Hᴴ * H = 1 := by rw [hH, hH2]
  set N := ∑ i, ∑ j, ‖Ti i j‖ with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set u' := H *ᵥ v with hu'
  set w := u' - proj H b' Ti u' with hw
  refine sq_le_of_pos hH hH2 b' hpos v w hv (herm_sub_proj hTi u') ?_ _ (by positivity) ?_
  · have e : herm H (u' - proj H b' Ti u') v = herm H u' v - herm H (proj H b' Ti u') v := by
      simp only [herm, mulVec_sub, dotProduct_sub]
    rw [hw, e, proj, herm_fam_mulVec,
      Finset.sum_eq_zero fun i _ => by rw [herm_swap hH, hv i, star_zero, zero_mul], sub_zero]
    unfold herm
    rw [hu', mulVec_mulVec, hH2, one_mulVec, star_dot_self]
  · refine (eucl_sub_le _ _).trans ?_
    have h1 : eucl u' = eucl v := eucl_mulVec_of_unitary hH' v
    have h2 := eucl_proj_le hH' b' b' Ti β β hβ hb' hb' u'
    rw [h1] at h2 ⊢
    have h2' : eucl (proj H b' Ti u') ≤ β * (N * (β * eucl v)) := h2
    have e : β * (N * (β * eucl v)) = N * β ^ 2 * eucl v := by ring
    linarith

theorem det_isUnit_of_herm {H s : Matrix (Fin n) (Fin n) ℂ} (hH2 : H * H = 1) (hs : sᴴ * H * s = H) :
    IsUnit s.det := by
  have h1 : H.det * H.det = 1 := by rw [← det_mul, hH2, det_one]
  have h2 := congrArg Matrix.det hs
  rw [det_mul, det_mul] at h2
  have hH0 : H.det ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
  have h3 : H.det * (s.det * sᴴ.det) = H.det * 1 := by rw [mul_one]; linear_combination h2
  exact IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hH0 h3)

theorem herm_mulVec_mulVec {H s : Matrix (Fin n) (Fin n) ℂ} (hs : sᴴ * H * s = H) (x y : Fin n → ℂ) :
    herm H (s *ᵥ x) (s *ᵥ y) = herm H x y := by
  unfold herm
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hs,
    ← dotProduct_mulVec]

theorem core {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (b : ι → Fin n → ℂ) (Ti : Matrix ι ι ℂ) (hTi : gram H b * Ti = 1)
    (hpos : ∀ y, (∀ i, herm H y (b i) = 0) → 0 ≤ (herm H y y).re)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ i, eucl (b i) ≤ M)
    (s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H)
    (β : ℝ) (hβ1 : 1 ≤ β) (hβ : ∀ i, eucl (s *ᵥ b i) ≤ β) (u : Fin n → ℂ) :
    eucl (s *ᵥ u) ≤ ((∑ i, ∑ j, ‖Ti i j‖) * M + (1 + ∑ i, ∑ j, ‖Ti i j‖) *
      (1 + (∑ i, ∑ j, ‖Ti i j‖) * M ^ 2)) * β ^ 2 * eucl u := by
  have hH' : Hᴴ * H = 1 := by rw [hH, hH2]
  set N := ∑ i, ∑ j, ‖Ti i j‖ with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ1
  set b' : ι → Fin n → ℂ := fun i => s *ᵥ b i with hb'
  have hiso : ∀ x y, herm H (s *ᵥ x) (s *ᵥ y) = herm H x y := herm_mulVec_mulVec hs
  have hgram : gram H b' = gram H b := by ext m i; exact hiso _ _
  have hdet := det_isUnit_of_herm hH2 hs
  have hpos' : ∀ y, (∀ i, herm H y (b' i) = 0) → 0 ≤ (herm H y y).re := fun y hy => by
    have e : y = s *ᵥ (s⁻¹ *ᵥ y) := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have := hpos (s⁻¹ *ᵥ y) fun i => by rw [← hiso, ← e]; exact hy i
    rwa [← hiso, ← e] at this
  set y := u - proj H b Ti u with hy
  have hyb : ∀ i, herm H y (b i) = 0 := herm_sub_proj hTi u
  have hv : ∀ i, herm H (s *ᵥ y) (b' i) = 0 := fun i => by
    show herm H (s *ᵥ y) (s *ᵥ b i) = 0
    rw [hiso]; exact hyb i
  have esplit : s *ᵥ u = s *ᵥ proj H b Ti u + s *ᵥ y := by rw [hy, mulVec_sub, add_sub_cancel]
  have h1 : eucl (s *ᵥ proj H b Ti u) ≤ β * (N * (M * eucl u)) := by
    rw [proj, mulVec_mulVec, mul_fam]
    exact eucl_proj_le hH' b b' Ti M β hβ0 hM hβ u
  have hy2 : eucl y ≤ (1 + N * M ^ 2) * eucl u := by
    refine (eucl_sub_le _ _).trans ?_
    have := eucl_proj_le hH' b b Ti M M hM0 hM hM u
    rw [proj]
    have e : M * (N * (M * eucl u)) = N * M ^ 2 * eucl u := by ring
    linarith
  have h2 := sq_le_compl hH hH2 b' Ti (hgram ▸ hTi) hpos' β hβ0 hβ (s *ᵥ y) hv
  rw [hiso] at h2
  have h3 : (herm H y y).re ≤ eucl y ^ 2 := herm_re_le hH' y
  have hA : 0 ≤ 1 + N * β ^ 2 := add_nonneg zero_le_one (mul_nonneg hN0 (sq_nonneg _))
  have hB : 0 ≤ 1 + N * M ^ 2 := add_nonneg zero_le_one (mul_nonneg hN0 (sq_nonneg _))
  have h4 : eucl (s *ᵥ y) ^ 2 ≤ ((1 + N * β ^ 2) * ((1 + N * M ^ 2) * eucl u)) ^ 2 := by
    calc eucl (s *ᵥ y) ^ 2 ≤ (1 + N * β ^ 2) ^ 2 * (herm H y y).re := h2
      _ ≤ (1 + N * β ^ 2) ^ 2 * eucl y ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ ≤ (1 + N * β ^ 2) ^ 2 * ((1 + N * M ^ 2) * eucl u) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (eucl_nonneg _) hy2 2) (sq_nonneg _)
      _ = _ := by ring
  have h5 : eucl (s *ᵥ y) ≤ (1 + N * β ^ 2) * ((1 + N * M ^ 2) * eucl u) :=
    (pow_le_pow_iff_left₀ (eucl_nonneg _) (mul_nonneg hA (mul_nonneg hB (eucl_nonneg _))) two_ne_zero).1 h4
  rw [esplit]
  refine (eucl_add_le _ _).trans ?_
  have hu0 := eucl_nonneg u
  have hb2 : β ≤ β ^ 2 := by nlinarith
  have hb3 : 1 + N * β ^ 2 ≤ (1 + N) * β ^ 2 := by nlinarith
  have e1 : β * (N * (M * eucl u)) ≤ β ^ 2 * (N * (M * eucl u)) :=
    mul_le_mul_of_nonneg_right hb2 (mul_nonneg hN0 (mul_nonneg hM0 hu0))
  have e2 : (1 + N * β ^ 2) * ((1 + N * M ^ 2) * eucl u) ≤ ((1 + N) * β ^ 2) * ((1 + N * M ^ 2) * eucl u) :=
    mul_le_mul_of_nonneg_right hb3 (mul_nonneg hB hu0)
  have e3 : β ^ 2 * (N * (M * eucl u)) + ((1 + N) * β ^ 2) * ((1 + N * M ^ 2) * eucl u) =
      (N * M + (1 + N) * (1 + N * M ^ 2)) * β ^ 2 * eucl u := by ring
  linarith

end GlobalTheory.SgInf.IsomBound

namespace GlobalTheory.SgInf

open IsomBound FrameBound

theorem continuous_eucl {N : ℕ} : Continuous (eucl : (Fin N → ℂ) → ℝ) := by
  unfold eucl
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    Complex.continuous_normSq.comp (continuous_apply i))

variable {k r : ℕ}

theorem continuous_gramVec (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    Continuous fun γ : Mat k r => gramVec k r z z' γ i := by
  cases i with
  | inl a => exact continuous_const
  | inr b => exact continuous_id.matrix_mulVec continuous_const

theorem continuous_gramM (z z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun γ : Mat k r => gramM k r z z' γ := by
  refine continuous_matrix fun i j => ?_
  unfold gramM herm
  exact (continuous_gramVec z z' i).star.dotProduct
    (continuous_const.matrix_mulVec (continuous_gramVec z z' j))

def isomConst (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : ℝ :=
  (∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) * (∑ i, eucl (gramVec k r z z' γ i)) +
    (1 + ∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) *
      (1 + (∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) * (∑ i, eucl (gramVec k r z z' γ i)) ^ 2)

theorem continuousOn_isomConst (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r))
    (hC : ∀ γ ∈ C, IsUnit (gramM k r z z' γ).det) : ContinuousOn (isomConst z z') C := by
  have hM : Continuous fun γ : Mat k r => ∑ i, eucl (gramVec k r z z' γ i) :=
    continuous_finsetSum _ fun i _ => continuous_eucl.comp (continuous_gramVec z z' i)
  have hN : ContinuousOn (fun γ : Mat k r => ∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) C := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ContinuousOn.norm ?_
    have e : ∀ γ ∈ C, (gramM k r z z' γ)⁻¹ i j =
        (gramM k r z z' γ).det⁻¹ * (gramM k r z z' γ).adjugate i j := fun γ _ => by
      rw [Matrix.inv_def, Ring.inverse_eq_inv]; rfl
    refine ContinuousOn.congr ?_ e
    refine ContinuousOn.mul (ContinuousOn.inv₀ ((continuous_gramM z z').matrix_det.continuousOn)
      fun γ hγ => (hC γ hγ).ne_zero) ?_
    exact ((continuous_gramM z z').matrix_adjugate.matrix_elem i j).continuousOn
  unfold isomConst
  exact (hN.mul hM.continuousOn).add ((continuousOn_const.add hN).mul
    (continuousOn_const.add (hN.mul (hM.pow 2).continuousOn)))

theorem isom_frame_bound : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → (∀ γ ∈ C, γ ∈ GG k r ∧ Gf k r z z' γ ≠ 0) → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ GG k r, ∀ B : ℝ, 1 ≤ B → (∀ i, eucl (s *ᵥ gramVec k r z z' γ i) ≤ B) → opn s ≤ C0 * B ^ 2 := by
  intro k r z z' C hz hz' hT hT' hC hreg
  have hR := fun γ (hγ : γ ∈ C) =>
    regular_pos_compl k r z z' γ hz hz' hT hT' (hreg γ hγ).1 (hreg γ hγ).2
  obtain ⟨C0, hC0⟩ := hC.exists_bound_of_continuousOn
    (continuousOn_isomConst z z' C fun γ hγ => (hR γ hγ).2.2.1)
  refine ⟨C0, fun γ hγ s hs B hB1 hB => ?_⟩
  obtain ⟨hH1, hH2, -⟩ := hpkFacts k r
  set N := ∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖ with hN
  set M := ∑ i, eucl (gramVec k r z z' γ i) with hM
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => eucl_nonneg _
  have hMi : ∀ i, eucl (gramVec k r z z' γ i) ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => eucl (gramVec k r z z' γ i)) (fun _ _ => eucl_nonneg _)
      (Finset.mem_univ i)
  have hTi : gram (Hpk k r) (gramVec k r z z' γ) * (gramM k r z z' γ)⁻¹ = 1 := by
    have e : gram (Hpk k r) (gramVec k r z z' γ) = gramM k r z z' γ := rfl
    rw [e]; exact mul_nonsing_inv _ (hR γ hγ).2.2.1
  have hpos : ∀ y, (∀ i, herm (Hpk k r) y (gramVec k r z z' γ i) = 0) →
      0 ≤ (herm (Hpk k r) y y).re := fun y hy => by
    by_cases h0 : y = 0
    · subst h0; simp [herm]
    · exact ((hR γ hγ).2.2.2 y h0 hy).le
  have key := fun u => core hH1 hH2 (gramVec k r z z' γ) (gramM k r z z' γ)⁻¹ hTi hpos M hM0 hMi s hs
    B hB1 hB u
  have eK : isomConst z z' γ = N * M + (1 + N) * (1 + N * M ^ 2) := rfl
  have hK0 : 0 ≤ isomConst z z' γ := by
    rw [eK]
    exact add_nonneg (mul_nonneg hN0 hM0) (mul_nonneg (add_nonneg zero_le_one hN0)
      (add_nonneg zero_le_one (mul_nonneg hN0 (sq_nonneg _))))
  have hK : isomConst z z' γ ≤ C0 := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hC0 γ hγ)
  have hB0 : 0 ≤ B ^ 2 := sq_nonneg _
  have hopn : opn s ≤ isomConst z z' γ * B ^ 2 := by
    unfold opn
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 hB0) fun x => ?_
    have h := key (WithLp.ofLp x)
    have e1 : eucl (s *ᵥ WithLp.ofLp x) = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) s x‖ := by rw [eucl_eq]; rfl
    have e2 : eucl (WithLp.ofLp x) = ‖x‖ := by rw [eucl_eq]
    rw [e1, e2] at h
    rw [eK]
    exact h
  exact hopn.trans (mul_le_mul_of_nonneg_right hK hB0)

end GlobalTheory.SgInf
