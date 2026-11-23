import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped MatrixGroups ModularForm Modular ComplexConjugate Real ArithmeticFunction.Moebius NumberTheorySymbols

namespace Ad3.S

namespace ScalarIntegralEstimates

lemma ee_add (x y : ℂ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

lemma ee_int (k : ℤ) : ee (k : ℂ) = 1 := by
  unfold ee; rw [show 2 * (π : ℂ) * I * (k : ℂ) = k * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma cpow_rmul (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) (y : ℂ) :
    ((r : ℂ) * x) ^ y = (r : ℂ) ^ y * x ^ y := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr' hx), Complex.log_ofReal_mul hr hx,
    Complex.cpow_def_of_ne_zero hr', Complex.cpow_def_of_ne_zero hx, ← Complex.exp_add,
    ← Complex.ofReal_log hr.le]
  ring_nf

lemma inv_cpow_half (X : ℂ) (hX : 0 < X.re) : X⁻¹ ^ (-(1 / 2 : ℂ)) = X ^ (1 / 2 : ℂ) := by
  rw [Complex.inv_cpow X _ (by rw [Ne, Complex.arg_eq_pi_iff]; intro h; linarith [h.1]),
    Complex.cpow_neg, inv_inv]

lemma sq_half (x : ℂ) (hx : x ≠ 0) : x ^ (1 / 2 : ℂ) * x ^ (1 / 2 : ℂ) = x := by
  rw [← Complex.cpow_add _ _ hx]; norm_num

lemma cpow_ne (x y : ℂ) (hx : x ≠ 0) : x ^ y ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hx]; exact Complex.exp_ne_zero _

end ScalarIntegralEstimates

namespace ScalarIntegralEstimates

lemma scal (z : ℂ) (c : ℤ) (d M ν : ℕ) (hz : 0 < z.im) (hd : 0 < d) (hM : 0 < M)
    (hcz : (c : ℂ) * z + d ≠ 0) (τ : ℂ) (hτ : τ = z / (d * ((c : ℂ) * z + d))) :
    (-2 * I * τ) ^ (-(1 / 2 : ℂ)) * ((2 * τ * ((M * d : ℕ) : ℂ)) ^ ν)⁻¹ * ((M * d : ℕ) : ℂ)⁻¹ =
      (d : ℂ) ^ (-(1 / 2 : ℂ)) * (-I * (d * (-1 / z) - c)) ^ (1 / 2 : ℂ) * (-I * (-1 / z)) ^ (-(1 / 2 : ℂ)) *
        ((d * (-1 / z) - c) / (-1 / z)) ^ ν * ((-2 * I * z) ^ (-(1 / 2 : ℂ)) * ((2 * z * M) ^ ν)⁻¹ * (M : ℂ)⁻¹) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hcz' : z * c + d ≠ 0 := by rw [mul_comm]; exact hcz
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hwim : 0 < (-1 / z).im := by
    have : (-1 / z).im = z.im / Complex.normSq z := by simp [Complex.div_im]; ring
    rw [this]; exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have hPre : 0 < (-I * (d * (-1 / z) - c)).re := by
    simp; positivity
  have hP0re : 0 < (-I * (-1 / z)).re := by
    simp; simpa using hwim
  set w := -1 / z with hw
  set P := -I * (d * w - c) with hP
  set P0 := -I * w with hP0
  have hPne : P ≠ 0 := fun h => by rw [h] at hPre; simp at hPre
  have hP0ne : P0 ≠ 0 := fun h => by rw [h] at hP0re; simp at hP0re
  have hwne : w ≠ 0 := by rw [hw]; exact div_ne_zero (by norm_num) hz0
  have hdwc : (d : ℂ) * w - c ≠ 0 := by intro h; apply hPne; rw [hP, h, mul_zero]
  have e1 : -2 * I * τ = (((d / 2 : ℝ) : ℂ) * P)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hτ, hP, hw]; push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have e2 : -2 * I * z = (((1 / 2 : ℝ) : ℂ) * P0)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hP0, hw]; push_cast; field_simp; ring_nf; rw [I_sq]; ring
  have hX1 : 0 < (((d / 2 : ℝ) : ℂ) * P).re := by
    rw [Complex.re_ofReal_mul]; exact mul_pos (by positivity) hPre
  have hX2 : 0 < (((1 / 2 : ℝ) : ℂ) * P0).re := by
    rw [Complex.re_ofReal_mul]; exact mul_pos (by norm_num) hP0re
  rw [e1, e2, inv_cpow_half _ hX1, inv_cpow_half _ hX2, cpow_rmul _ (by positivity) _ hPne,
    cpow_rmul _ (by norm_num) _ hP0ne]
  rw [show ((d / 2 : ℝ) : ℂ) = ((d : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg (by positivity) (by norm_num), Complex.ofReal_natCast]
  have hτne : τ ≠ 0 := by rw [hτ]; exact div_ne_zero hz0 (mul_ne_zero hdC hcz)
  have hK : (2 * z * M : ℂ) = 2 * τ * ((M * d : ℕ) : ℂ) * ((d * w - c) / w) := by
    rw [hτ, hw]; push_cast; field_simp; ring
  rw [hK, mul_pow (2 * τ * ((M * d : ℕ) : ℂ)) ((d * w - c) / w) ν, Complex.cpow_neg, Complex.cpow_neg P0]
  have hs := sq_half (d : ℂ) hdC
  have hsne := cpow_ne (d : ℂ) (1 / 2) hdC
  have hqne := cpow_ne P0 (1 / 2) hP0ne
  have htne := cpow_ne ((1 / 2 : ℝ) : ℂ) (1 / 2) (by norm_num)
  have hKne : (2 * τ * ((M * d : ℕ) : ℂ)) ^ ν ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hτne) (by push_cast; exact mul_ne_zero hMC hdC))
  have hRne : ((d * w - c) / w) ^ ν ≠ 0 := pow_ne_zero _ (div_ne_zero hdwc hwne)
  generalize (d : ℂ) ^ (1 / 2 : ℂ) = s at *
  generalize P0 ^ (1 / 2 : ℂ) = q at *
  generalize (2 * τ * ((M * d : ℕ) : ℂ)) ^ ν = K at *
  generalize ((d * w - c) / w) ^ ν = R at *
  generalize ((1 / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = t at *
  generalize P ^ (1 / 2 : ℂ) = p at *
  push_cast
  field_simp
  linear_combination p * hs

end ScalarIntegralEstimates

open ScalarIntegralEstimates in
theorem third_estimate_of_first_two : T1 → T2 → T3 := by
  intro h1 h2 M d ν _ ψ c' γ z hd hν hc hdd
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdet : γ 0 0 * d - γ 0 1 * (4 * (M : ℤ) ^ 2 * c') = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    rw [← hc, ← hdd]; exact this
  have hdetC : (γ 0 0 : ℂ) * d - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    rw [hc]; exact_mod_cast hdet
  have hzC : (z : ℂ) ≠ 0 := z.ne_zero
  have hzim : 0 < (z : ℂ).im := z.im_pos
  have hcz : (γ 1 0 : ℂ) * z + d ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    rcases h' with h0 | h0
    · rw [h0] at h; simp at h; exact hd.ne' h
    · exact z.im_pos.ne' h0
  set τ : ℂ := (z : ℂ) / (d * ((γ 1 0 : ℂ) * z + d)) with hτ
  have hγz : ((γ • z : ℍ) : ℂ) = (γ 0 1 : ℂ) / d + τ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
    rw [hτ, hdd]; push_cast
    have hcz' : (z : ℂ) * (γ 1 0 : ℂ) + d ≠ 0 := by rw [mul_comm]; exact hcz
    field_simp
    linear_combination (z : ℂ) * hdetC
  have hτim : 0 < τ.im := by
    have := (γ • z).im_pos
    rw [show τ = ((γ • z : ℍ) : ℂ) - (γ 0 1 : ℂ) / d by rw [hγz]; ring]
    simpa using this
  set Q : ℤ → ℂ := fun n => ψ (n : ZMod M) * ee ((γ 0 1 : ℂ) * (n : ℂ) ^ 2 / d) with hQ
  have hQper : ∀ x, Q (x + ((M * d : ℕ) : ℤ)) = Q x := by
    intro x; simp only [hQ]; congr 1
    · push_cast; simp
    · rw [show (γ 0 1 : ℂ) * (((x + ((M * d : ℕ) : ℤ) : ℤ) : ℂ)) ^ 2 / d =
          (γ 0 1 : ℂ) * (x : ℂ) ^ 2 / d + ((γ 0 1 * (2 * x * M + M ^ 2 * d) : ℤ) : ℂ) by
          push_cast; field_simp; ring, ee_add, ee_int, mul_one]
  have hth : th (fun n => ψ (n : ZMod M)) ν (γ • z : ℍ) = th Q ν τ := by
    unfold th; rw [hγz]; congr 1; ext n; simp only [hQ]
    rw [show (n : ℂ) ^ 2 * ((γ 0 1 : ℂ) / d + τ) = (γ 0 1 : ℂ) * (n : ℂ) ^ 2 / d + (n : ℂ) ^ 2 * τ by ring,
      ee_add]
    ring
  rw [hth, h1 Q (M * d) ν τ (by positivity) hν hτim hQper,
    h1 (fun n => ψ (n : ZMod M)) M ν z hMpos hν hzim (by intro x; push_cast; simp)]
  have hin : ∀ n : ℤ, ∑ x ∈ Finset.range (M * d), Q x * ee (n * x / ((M * d : ℕ) : ℂ)) =
      ψ d * GS (γ 0 1) d * ee (c' * (n : ℂ) ^ 2 / d) *
        ∑ x ∈ Finset.range M, ψ (((x : ℕ) : ℤ) : ZMod M) * ee (n * x / M) := by
    intro n; simp only [Int.cast_natCast]
    rw [← h2 M d ψ (γ 0 0) (γ 0 1) c' n hd hdet]
    apply Finset.sum_congr rfl; intro x _; simp [hQ]
  have hcC : ((γ 1 0 : ℤ) : ℂ) = 4 * (M : ℂ) ^ 2 * c' := by rw [hc]; push_cast; ring
  have hcz2 : 4 * (M : ℂ) ^ 2 * c' * z + d ≠ 0 := by rw [← hcC]; exact hcz
  have hex : ∀ n : ℤ, ee (c' * (n : ℂ) ^ 2 / d) * ee (-((n : ℂ) ^ 2 / (4 * ((M * d : ℕ) : ℂ) ^ 2 * τ))) =
      ee (-((n : ℂ) ^ 2 / (4 * (M : ℂ) ^ 2 * z))) := by
    intro n; rw [← ee_add]; congr 1; rw [hτ, hcC]; push_cast; field_simp; ring
  have hsum : ∑' n : ℤ, (∑ x ∈ Finset.range (M * d), Q x * ee (n * x / ((M * d : ℕ) : ℂ))) * (n : ℂ) ^ ν *
      ee (-((n : ℂ) ^ 2 / (4 * ((M * d : ℕ) : ℂ) ^ 2 * τ))) = ψ d * GS (γ 0 1) d *
      ∑' n : ℤ, (∑ x ∈ Finset.range M, ψ (((x : ℕ) : ℤ) : ZMod M) * ee (n * x / M)) * (n : ℂ) ^ ν *
        ee (-((n : ℂ) ^ 2 / (4 * (M : ℂ) ^ 2 * z))) := by
    rw [← tsum_mul_left]; congr 1; ext n; rw [hin n, ← hex n]; ring
  rw [hsum, scal z (γ 1 0) d M ν hzim hd hMpos hcz τ hτ]; ring

end Ad3.S

end
