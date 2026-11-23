import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open Complex

namespace GlobalTheory.CompanionTheory.RankinSelberg.RealGamma

lemma gammaR_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h := (differentiable_Gammaℝ_inv s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
  have e : (fun z : ℂ => (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := by
    funext z; simp
  rwa [e] at h

lemma gammaC_eq : Gammaℂ = fun s => Gammaℝ s * Gammaℝ (s + 1) := by
  funext s; exact (Gammaℝ_mul_Gammaℝ_add_one s).symm

lemma gammaC_ne_zero {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [gammaC_eq]
  refine mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos ?_)
  simp only [add_re, one_re]; linarith

lemma gammaC_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℂ s := by
  rw [gammaC_eq]
  have h1 : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (z + 1)) s :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := Gammaℝ) (f := fun z : ℂ => z + 1) s
      (gammaR_differentiableAt h1) (differentiableAt_id.add_const 1)
  exact (gammaR_differentiableAt hs).mul h2

lemma shift_re_pos {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) : 0 < (s + (k : ℂ) - 1).re := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [sub_re, add_re, natCast_re, one_re]; linarith

lemma shift_differentiableAt {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => Gammaℂ (z + (k : ℂ) - 1)) s :=
  DifferentiableAt.comp (𝕜 := ℂ) (g := Gammaℂ) (f := fun z : ℂ => z + (k : ℂ) - 1) s
    (gammaC_differentiableAt (shift_re_pos hk hs))
    ((differentiableAt_id.add_const _).sub_const 1)

lemma GG_differentiableAt {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Ad3.R.GG k) s :=
  (gammaC_differentiableAt hs).mul (shift_differentiableAt hk hs)

lemma GG_ne_zero {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) : Ad3.R.GG k s ≠ 0 :=
  mul_ne_zero (gammaC_ne_zero hs) (gammaC_ne_zero (shift_re_pos hk hs))

lemma tail_re_pos (δ : Bool) {s : ℂ} (hs : 0 < s.re) : 0 < (s + if δ then 0 else 1 : ℂ).re := by
  cases δ <;> simp <;> linarith

lemma lR_ne_zero {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : 0 < s.re) : Ad3.lR k δ s ≠ 0 :=
  mul_ne_zero (gammaC_ne_zero (shift_re_pos hk hs)) (Gammaℝ_ne_zero_of_re_pos (tail_re_pos δ hs))

lemma lR_differentiableAt {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Ad3.lR k δ) s := by
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (z + if δ then 0 else 1)) s :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := Gammaℝ) (f := fun z : ℂ => z + if δ then 0 else 1) s
      (gammaR_differentiableAt (tail_re_pos δ hs)) (differentiableAt_id.add_const _)
  exact (shift_differentiableAt hk hs).mul h2

lemma gamR_differentiableAt {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : Ad3.R.Strip s) :
    DifferentiableAt ℂ (Ad3.gamR k δ) s := by
  have h1 : 0 < (1 - s).re := by simp only [sub_re, one_re]; linarith [hs.2]
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Ad3.lR k δ (1 - z)) s :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := Ad3.lR k δ) (f := fun z : ℂ => 1 - z) s
      (lR_differentiableAt hk δ h1) (differentiableAt_id.const_sub 1)
  exact (h2.const_mul _).div (lR_differentiableAt hk δ hs.1) (lR_ne_zero hk δ hs.1)

lemma negI_pow_two_mul (k : ℕ) : (-I) ^ (2 * k) = (-1 : ℂ) ^ k := by
  rw [pow_mul]; simp

lemma gamma_identity {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : Ad3.R.Strip s) :
    (-1) ^ k * Ad3.R.GG k (1 - s) * Gammaℝ (s + if δ then 1 else 0) =
      Ad3.gamR k δ s * Ad3.R.GG k s * ((if δ then -I else 1) * Gammaℝ (1 - s + if δ then 1 else 0)) := by
  have hne := lR_ne_zero hk δ hs.1
  have hG := gammaC_ne_zero (shift_re_pos hk hs.1)
  have hC1 := Gammaℝ_mul_Gammaℝ_add_one s
  have hC2 := Gammaℝ_mul_Gammaℝ_add_one (1 - s)
  unfold Ad3.gamR Ad3.R.GG
  cases δ with
  | false =>
    have hR : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith [hs.1])
    simp only [Bool.false_eq_true, if_false, add_zero, tsub_zero, one_mul, Ad3.lR] at *
    rw [negI_pow_two_mul, ← hC1, ← hC2]
    field_simp
  | true =>
    have hR : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs.1
    have hp : (-I) ^ (2 * k - 1) * (-I) = (-1 : ℂ) ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), negI_pow_two_mul]
    simp only [if_true, add_zero, Ad3.lR] at *
    rw [← hp, ← hC1, ← hC2]
    field_simp

theorem main : Ad3.R.RealPlaceGammaFactors := by
  intro k δ hk
  refine ⟨fun s hs => (GG_differentiableAt hk hs).differentiableWithinAt,
    fun s hs => GG_ne_zero hk hs,
    fun s hs => (gamR_differentiableAt hk δ hs).differentiableWithinAt,
    fun s hs => gamma_identity hk δ hs⟩

end GlobalTheory.CompanionTheory.RankinSelberg.RealGamma

end
