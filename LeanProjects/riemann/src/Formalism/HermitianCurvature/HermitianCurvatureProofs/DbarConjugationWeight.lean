import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount

open Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem weight_inverse : C7.WInv := by
  intro TT ζ hTT hG
  unfold C7.GGz at hG
  have hq : 0 < Complex.normSq ζ := by linarith
  have hζ : ζ ≠ 0 := by intro h; rw [h, Complex.normSq_zero] at hq; exact lt_irrefl _ hq
  have hcζ : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).2 hζ
  constructor
  · unfold C7.Wz C7.GGz
    push_cast
    rw [inv_div, ← Complex.mul_conj]
    field_simp
  · have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
    rw [norm_div, norm_one, one_div]
    rw [inv_lt_inv₀ hn (Real.sqrt_pos.2 hTT), Real.sqrt_lt' hn, ← Complex.normSq_eq_norm_sq]
    linarith

theorem weight_exactness : C7.WExact := by
  intro TT Dr ζ h; unfold C7.Wz; rw [Complex.normSq_mul]
  have : Complex.normSq Dr ≠ 0 := by simpa using h
  rw [mul_div_mul_left _ _ this]

theorem normal_form_weight : C7.NFWeight := by
  intro N i i' D Gv c hD hG hc hii
  have hd : 0 < ‖D‖ := norm_pos_iff.2 hD
  have h1 : ‖D ^ i * (starRingEnd ℂ) D ^ i'‖ = (‖D‖ ^ N)⁻¹ := by
    rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_conj, ← zpow_add₀ hd.ne', hii, zpow_neg, zpow_natCast]
  have hGN : 0 < Gv ^ ((N : ℝ) / 2) := Real.rpow_pos_of_pos hG _
  have key : (Complex.normSq D / Gv) ^ N * c = (‖D‖ ^ N * (Gv ^ ((N : ℝ) / 2))⁻¹) ^ 2 * c := by
    have e : (Gv ^ ((N : ℝ) / 2)) ^ 2 = Gv ^ N := by
      rw [← Real.rpow_natCast (Gv ^ ((N : ℝ) / 2)) 2, ← Real.rpow_mul hG.le]
      norm_num
    rw [mul_pow, inv_pow, e, Complex.normSq_eq_norm_sq, div_pow, ← pow_mul, ← pow_mul, mul_comm 2 N]
    ring
  rw [key, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), h1, neg_div, Real.rpow_neg hG.le]
  field_simp

theorem leibniz_log_derivative : C7.LdLeibniz := by
  intro f g p x hf hg
  unfold LE.ld
  have hle : ((p : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have e : (fun u : ℝ => (fun y => f y * g y) (Real.exp u)) =
      (fun u => f (Real.exp u)) * (fun u => g (Real.exp u)) := rfl
  rw [e, iteratedDeriv_mul ((hf.of_le hle).contDiffAt) ((hg.of_le hle).contDiffAt)]

theorem dbar_conjugation_weight : C7.DbarConjW := by
  intro TT N f ζ hTT hG hf
  unfold C7.GGz at hG
  have hq : 0 < Complex.normSq ζ := by linarith
  have hζ : ζ ≠ 0 := by intro h; rw [h, Complex.normSq_zero] at hq; exact lt_irrefl _ hq
  let q : ℂ → ℝ := fun x => x.re * x.re + x.im * x.im
  have hqn : ∀ x, Complex.normSq x = q x := fun x => Complex.normSq_apply x
  have hWfun : (fun x => ((C7.Wz TT x : ℝ) : ℂ) ^ N * f x) =
      fun x => (((q x / (q x - TT)) ^ N : ℝ) : ℂ) * f x := by
    funext x; simp only [C7.Wz, C7.GGz, hqn]; push_cast; ring
  have hre : HasFDerivAt (fun x : ℂ => x.re) Complex.reCLM ζ := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun x : ℂ => x.im) Complex.imCLM ζ := Complex.imCLM.hasFDerivAt
  have hqd : HasFDerivAt q ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) +
      (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM)) ζ := (hre.mul hre).add (him.mul him)
  have hq0 : q ζ - TT ≠ 0 := by rw [← hqn]; linarith
  have hφ : HasDerivAt (fun s : ℝ => (s / (s - TT)) ^ N)
      ((N : ℝ) * (q ζ / (q ζ - TT)) ^ (N - 1) * ((1 * (q ζ - TT) - q ζ * 1) / (q ζ - TT) ^ 2)) (q ζ) :=
    ((hasDerivAt_id (q ζ)).div ((hasDerivAt_id (q ζ)).sub_const TT) hq0).pow N
  have hWc := Complex.ofRealCLM.hasFDerivAt.comp ζ (hφ.comp_hasFDerivAt ζ hqd)
  have hP : HasFDerivAt (fun x => (((q x / (q x - TT)) ^ N : ℝ) : ℂ) * f x) _ ζ := hWc.mul hf.hasFDerivAt
  unfold C7.dbar
  rw [hWfun, hP.fderiv]
  simp
  have hWz : ((C7.Wz TT ζ : ℝ) : ℂ) = ((q ζ : ℝ) : ℂ) / (((q ζ : ℝ) : ℂ) - TT) := by
    simp only [C7.Wz, C7.GGz, hqn]; push_cast; ring
  have hGz : ((C7.GGz TT ζ : ℝ) : ℂ) = ((q ζ : ℝ) : ℂ) - TT := by
    simp only [C7.GGz, hqn]; push_cast; ring
  have hQ : ((q ζ : ℝ) : ℂ) = ζ * (starRingEnd ℂ) ζ := by rw [← hqn, Complex.mul_conj]
  have hc : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).2 hζ
  have hd : ζ * (starRingEnd ℂ) ζ - TT ≠ 0 := by rw [← hQ]; exact_mod_cast hq0
  rw [hWz, hGz, hQ, Complex.re_eq_add_conj, Complex.im_eq_sub_conj]
  rcases N with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]; push_cast
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hre2 : (ζ + (starRingEnd ℂ) ζ) / 2 + (ζ + (starRingEnd ℂ) ζ) / 2 + Complex.I *
        ((ζ - (starRingEnd ℂ) ζ) / (2 * Complex.I) + (ζ - (starRingEnd ℂ) ζ) / (2 * Complex.I)) = 2 * ζ := by
      field_simp; ring
    have hW : (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ (m + 1) /
        ((starRingEnd ℂ) ζ * (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) =
        (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ m * ζ /
          (ζ * (starRingEnd ℂ) ζ - (TT : ℂ)) ^ 2 := by
      rw [pow_succ]
      generalize (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ m = P
      field_simp
    linear_combination (f ζ * (((m : ℂ) + 1) * (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ m *
        (-(TT : ℂ) / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ)) ^ 2)) / 2) * hre2 +
      (((m : ℂ) + 1) * (TT : ℂ) * f ζ) * hW

end Formalism.FourierDecayAlt.P
