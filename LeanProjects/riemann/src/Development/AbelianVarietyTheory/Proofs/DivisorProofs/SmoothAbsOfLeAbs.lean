import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.RegMaxA

open scoped ComplexOrder Matrix

namespace GlobalTheory.RegularisedMaxTwo

open ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

def smoothAbs (η x : ℝ) : ℝ := 2 * η * rmRho (x / (2 * η))

def regMaxTwo (η : ℝ) (p : ℝ × ℝ) : ℝ := (p.1 + p.2) / 2 + smoothAbs η (p.1 - p.2) / 2

lemma smoothAbs_bounds {η : ℝ} (hη : 0 < η) (x : ℝ) :
    |x| ≤ smoothAbs η x ∧ smoothAbs η x ≤ |x| + 2 * η := by
  have h2 : 0 < 2 * η := by linarith
  have h := rmRho_bounds (x / (2 * η))
  rw [abs_div, abs_of_pos h2] at h
  have e : 2 * η * (|x| / (2 * η)) = |x| := by field_simp
  unfold smoothAbs
  constructor
  · have := mul_le_mul_of_nonneg_left h.1 h2.le
    rw [e] at this; exact this
  · have := mul_le_mul_of_nonneg_left h.2 h2.le
    rw [mul_add, e, mul_one] at this; exact this

lemma smoothAbs_lip {η : ℝ} (hη : 0 < η) (s t : ℝ) :
    |smoothAbs η s - smoothAbs η t| ≤ |s - t| := by
  have h2 : 0 < 2 * η := by linarith
  rw [show smoothAbs η s - smoothAbs η t = 2 * η * (rmRho (s / (2 * η)) - rmRho (t / (2 * η))) by
    unfold smoothAbs; ring, abs_mul, abs_of_pos h2]
  calc 2 * η * |rmRho (s / (2 * η)) - rmRho (t / (2 * η))|
      ≤ 2 * η * |s / (2 * η) - t / (2 * η)| := mul_le_mul_of_nonneg_left (rmRho_lip _ _) h2.le
    _ = |s - t| := by rw [← sub_div, abs_div, abs_of_pos h2]; field_simp

lemma smoothAbs_of_le_abs {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : 2 * η ≤ |x|) :
    smoothAbs η x = |x| := by
  have h2 : 0 < 2 * η := by linarith
  have h : 1 / 2 ≤ |x / (2 * η)| := by
    rw [abs_div, abs_of_pos h2, le_div_iff₀ h2]; linarith
  unfold smoothAbs
  rw [rmRho_of_abs _ h, abs_div, abs_of_pos h2]
  field_simp

lemma rmRho_convexOn : ConvexOn ℝ Set.univ rmRho :=
  Monotone.convexOn_univ_of_deriv (fun t => (rmRho_hasDerivAt t).differentiableAt)
    (by rw [rmRho_deriv]; exact rmRho'_monotone)

lemma regMaxTwo_contDiff (η : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (regMaxTwo η) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (smoothAbs η) := by
    unfold smoothAbs
    exact contDiff_const.mul (rmRho_contDiff.comp (contDiff_id.div_const _))
  unfold regMaxTwo
  exact ((contDiff_fst.add contDiff_snd).div_const _).add
    ((hs.comp (contDiff_fst.sub contDiff_snd)).div_const _)

lemma regMaxTwo_convexOn {η : ℝ} (hη : 0 < η) : ConvexOn ℝ Set.univ (regMaxTwo η) := by
  have h2 : 0 < 2 * η := by linarith
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have key := rmRho_convexOn.2 (Set.mem_univ ((x.1 - x.2) / (2 * η)))
    (Set.mem_univ ((y.1 - y.2) / (2 * η))) ha hb hab
  simp only [smul_eq_mul] at key
  have k2 := mul_le_mul_of_nonneg_left key h2.le
  simp only [regMaxTwo, smoothAbs, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd]
  have harg : (a * x.1 + b * y.1 - (a * x.2 + b * y.2)) / (2 * η) =
      a * ((x.1 - x.2) / (2 * η)) + b * ((y.1 - y.2) / (2 * η)) := by
    field_simp; ring
  rw [harg]
  nlinarith [k2]

lemma regMaxTwo_monotone {η : ℝ} (hη : 0 < η) : Monotone (regMaxTwo η) := by
  intro p q hpq
  have h1 : p.1 ≤ q.1 := hpq.1
  have h2 : p.2 ≤ q.2 := hpq.2
  have L := (abs_le.mp (smoothAbs_lip hη (q.1 - q.2) (p.1 - p.2))).1
  have : |q.1 - q.2 - (p.1 - p.2)| ≤ (q.1 - p.1) + (q.2 - p.2) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [regMaxTwo]
  linarith

theorem exists_regMaxTwo : ∀ η : ℝ, 0 < η → ∃ m : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) m ∧
    ConvexOn ℝ Set.univ m ∧ Monotone m ∧ (∀ a b, max a b ≤ m (a, b) ∧ m (a, b) ≤ max a b + η) ∧
    (∀ a b, b + 2 * η ≤ a → m (a, b) = a) ∧ (∀ a b, a + 2 * η ≤ b → m (a, b) = b) ∧
    ∀ a b c, m (a + c, b + c) = m (a, b) + c := by
  intro η hη
  refine ⟨regMaxTwo η, regMaxTwo_contDiff η, regMaxTwo_convexOn hη, regMaxTwo_monotone hη,
    ?_, ?_, ?_, ?_⟩
  · intro a b
    have hb := smoothAbs_bounds hη (a - b)
    simp only [regMaxTwo]
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      rw [abs_of_nonpos (by linarith : a - b ≤ 0)] at hb
      constructor <;> linarith [hb.1, hb.2]
    · rw [max_eq_left h]
      rw [abs_of_nonneg (by linarith : 0 ≤ a - b)] at hb
      constructor <;> linarith [hb.1, hb.2]
  · intro a b hab
    have h0 : 0 ≤ a - b := by linarith
    have e := smoothAbs_of_le_abs hη (x := a - b) (by rw [abs_of_nonneg h0]; linarith)
    rw [abs_of_nonneg h0] at e
    simp only [regMaxTwo, e]
    ring
  · intro a b hab
    have h0 : a - b ≤ 0 := by linarith
    have e := smoothAbs_of_le_abs hη (x := a - b) (by rw [abs_of_nonpos h0]; linarith)
    rw [abs_of_nonpos h0] at e
    simp only [regMaxTwo, e]
    ring
  · intro a b c
    simp only [regMaxTwo]
    rw [show a + c - (b + c) = a - b by ring]
    ring

end

end GlobalTheory.RegularisedMaxTwo
