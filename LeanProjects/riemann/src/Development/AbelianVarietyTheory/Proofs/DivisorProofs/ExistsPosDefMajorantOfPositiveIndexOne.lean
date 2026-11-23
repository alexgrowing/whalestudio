import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
open Matrix GlobalTheory.LKTrip

namespace GlobalTheory.HermitianMajorantIdentities

theorem mul_vecMulVec_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    A * vecMulVec u v * B = vecMulVec (A *ᵥ u) (v ᵥ* B) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem form_vecMulVec {n : ℕ} (u x : Fin n → ℂ) :
    star x ⬝ᵥ vecMulVec u (star u) *ᵥ x = (star x ⬝ᵥ u) * (star u ⬝ᵥ x) := by
  rw [vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]

theorem herm_swap {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ H *ᵥ x = star (star x ⬝ᵥ H *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hH.eq, ← dotProduct_mulVec]

end GlobalTheory.HermitianMajorantIdentities

namespace GlobalTheory

open GlobalTheory.HermitianMajorantIdentities in

theorem exists_posDef_majorant_of_sigPosH_eq_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  intro n H hH hdet hsig z hz
  set a : ℝ := (star z ⬝ᵥ H *ᵥ z).re with ha
  have hzz : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := by
    have h := herm_swap hH z z
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  set u : Fin n → ℂ := H *ᵥ z with hu
  have hux : ∀ x, star u ⬝ᵥ x = star z ⬝ᵥ H *ᵥ x := by
    intro x; rw [hu, star_mulVec, hH.eq, ← dotProduct_mulVec]
  refine ⟨((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, hH.eq, conjTranspose_vecMulVec, star_star]
    simp [Complex.star_def]
  · intro x hx
    set q := star z ⬝ᵥ H *ᵥ x with hq
    set t : ℂ := q / (a : ℂ) with ht
    set x' := x - t • z with hx'
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hzx' : star z ⬝ᵥ H *ᵥ x' = 0 := by
      rw [hx', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hzz, ← hq, ht, smul_eq_mul]
      field_simp; ring
    have hx'z : star x' ⬝ᵥ H *ᵥ z = 0 := by
      rw [herm_swap hH z x', hzx', star_zero]
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have hxe : x = t • z + x' := by rw [hx']; abel
    have hxx : star x ⬝ᵥ H *ᵥ x = star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x' := by
      conv_lhs => rw [hxe]
      simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hzx', hx'z, hzz']
      ring
    have hxz : star x ⬝ᵥ H *ᵥ z = star q := herm_swap hH z x
    have hP : star x ⬝ᵥ (((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H) *ᵥ x
        = ((2 / a : ℝ) : ℂ) * (star q * q) - (star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x') := by
      rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, form_vecMulVec, hux, hxx,
        smul_eq_mul]
      rw [show star x ⬝ᵥ u = star q from hxz]
    have hqt : q = t * (a : ℂ) := by rw [ht]; field_simp
    have hnt : star t * t = ((Complex.normSq t : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hP, hqt, star_mul', Complex.star_def, Complex.conj_ofReal]
    have e1 : ((starRingEnd ℂ) t * (a : ℂ) * (t * (a : ℂ))) = ((Complex.normSq t * a * a : ℝ) : ℂ) := by
      rw [← Complex.star_def, show star t * (a:ℂ) * (t * (a:ℂ)) = (star t * t) * ((a * a : ℝ) : ℂ) by push_cast; ring, hnt]
      push_cast; ring
    rw [e1, ← Complex.star_def, hnt]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_mul]
    have hapos : 0 < a := hz
    by_cases h0 : x' = 0
    · have htne : t ≠ 0 := by
        intro ht0
        apply hx
        rw [hxe, h0, ht0, zero_smul, add_zero]
      have hnpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr htne
      rw [h0]
      simp only [star_zero, zero_dotProduct, Complex.zero_re, add_zero]
      field_simp
      nlinarith [mul_pos hnpos hapos]
    · have hneg := re_form_neg_of_orth_of_sigPosH_eq_one H hH hdet hsig z x' hz hzx' h0
      have hn0 : 0 ≤ Complex.normSq t := Complex.normSq_nonneg t
      have : 2 / a * (Complex.normSq t * a * a) - Complex.normSq t * a = Complex.normSq t * a := by
        field_simp; ring
      nlinarith [mul_nonneg hn0 hapos.le]
  · intro Y s c hs hY hYz
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hA : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = (s : ℂ) * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hY,
        smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hB : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = star c * (star z ⬝ᵥ H *ᵥ (Y *ᵥ x)) := by
      intro x
      rw [hYz, star_smul, smul_dotProduct, smul_eq_mul]
    have hsc : (s : ℂ) = star c * c := by
      have h1 := (hA z).symm.trans (hB z)
      rw [hYz, mulVec_smul, dotProduct_smul, smul_eq_mul, hzz'] at h1
      have h2 : ((s : ℂ) - star c * c) * (a : ℂ) = 0 := by rw [sub_mul, h1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha0)
    have hc0 : star c ≠ 0 := by
      intro h0
      have : (s : ℂ) = 0 := by rw [hsc, h0, zero_mul]
      exact hs.ne' (by exact_mod_cast this)
    have hrow : ∀ x, star z ⬝ᵥ H *ᵥ (Y *ᵥ x) = c * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      have h1 := (hA x).symm.trans (hB x)
      rw [hsc, mul_assoc] at h1
      exact (mul_left_cancel₀ hc0 h1).symm
    have hrowv : star u ᵥ* Y = c • star u := by
      funext j
      have h1 : (star u ᵥ* Y) ⬝ᵥ Pi.single j 1 = (c • star u) ⬝ᵥ Pi.single j 1 := by
        rw [← dotProduct_mulVec, hux, hrow, smul_dotProduct, hux, smul_eq_mul]
      simpa [dotProduct_single] using h1
    have hcolv : Yᴴ *ᵥ u = star c • u := by
      have h1 := congrArg star hrowv
      rw [star_vecMul, star_star, star_smul, star_star] at h1
      exact h1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul', hcolv,
      hrowv, hY]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hsc]
    ring

end GlobalTheory
