import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory

theorem norm_mulVec_le_of_abs_le {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (Λ : ℝ)
    (hY : ∀ i j, |Y i j| ≤ Λ) (v : Fin g → ℝ) : ‖Y *ᵥ v‖ ≤ (g : ℝ) * Λ * ‖v‖ := by
  have hΛ : ∀ i j, 0 ≤ Λ := fun i j => (abs_nonneg _).trans (hY i j)
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg; simp [Subsingleton.elim (Y *ᵥ v) 0]
  have hΛ0 : 0 ≤ Λ := hΛ ⟨0, hg⟩ ⟨0, hg⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  calc |(Y *ᵥ v) i| = |∑ j, Y i j * v j| := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, |Y i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin g, Λ * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hY i j) (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j)
          (abs_nonneg _) hΛ0
    _ = (g : ℝ) * Λ * ‖v‖ := by simp [Finset.sum_const]; ring

theorem dotProduct_le_card_mul_norm {g : ℕ} (v x : Fin g → ℝ) :
    v ⬝ᵥ x ≤ (g : ℝ) * ‖v‖ * ‖x‖ := by
  calc v ⬝ᵥ x ≤ |v ⬝ᵥ x| := le_abs_self _
    _ ≤ ∑ j, |v j * x j| := by simp only [dotProduct]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin g, ‖v‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _) (norm_nonneg _)
    _ = (g : ℝ) * ‖v‖ * ‖x‖ := by simp [Finset.sum_const]; ring

theorem quadForm_inverse_compare {g : ℕ} (A Y : Matrix (Fin g) (Fin g) ℝ) (c D Λ : ℝ)
    (hYA : Y * A = 1) (hc : 0 < c) (hD : 0 ≤ D) (hY : ∀ i j, |Y i j| ≤ Λ)
    (hq : ∀ v : Fin g → ℝ, c * ‖v‖ ^ 2 ≤ D * (v ⬝ᵥ (Y *ᵥ v))) (x : Fin g → ℝ) :
    c * ‖x‖ ^ 2 ≤ D * ((g : ℝ) * Λ) ^ 2 * (x ⬝ᵥ (A *ᵥ x)) ∧
      c * (x ⬝ᵥ (A *ᵥ x)) ≤ (g : ℝ) ^ 2 * D * ‖x‖ ^ 2 := by
  set v := A *ᵥ x with hv
  have hYv : Y *ᵥ v = x := by rw [hv, Matrix.mulVec_mulVec, hYA, Matrix.one_mulVec]
  have hnx : ‖x‖ ≤ (g : ℝ) * Λ * ‖v‖ := hYv ▸ norm_mulVec_le_of_abs_le Y Λ hY v
  have hqv := hq v
  rw [hYv] at hqv
  have hs := dotProduct_le_card_mul_norm v x
  rw [dotProduct_comm x v]
  set s := v ⬝ᵥ x
  have hn := norm_nonneg v
  have hm := norm_nonneg x
  have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  constructor
  · have h1 : ‖x‖ ^ 2 ≤ ((g : ℝ) * Λ * ‖v‖) ^ 2 := pow_le_pow_left₀ hm hnx 2
    calc c * ‖x‖ ^ 2 ≤ c * ((g : ℝ) * Λ * ‖v‖) ^ 2 := mul_le_mul_of_nonneg_left h1 hc.le
      _ = ((g : ℝ) * Λ) ^ 2 * (c * ‖v‖ ^ 2) := by ring
      _ ≤ ((g : ℝ) * Λ) ^ 2 * (D * s) := mul_le_mul_of_nonneg_left hqv (sq_nonneg _)
      _ = D * ((g : ℝ) * Λ) ^ 2 * s := by ring
  · rcases hn.eq_or_lt with h0 | hpos
    · have : s ≤ 0 := by rw [← h0] at hs; simpa using hs
      have : c * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le this
      exact this.trans (by positivity)
    · have hcn : c * ‖v‖ ≤ D * g * ‖x‖ := by
        have : (c * ‖v‖) * ‖v‖ ≤ (D * g * ‖x‖) * ‖v‖ := by
          calc (c * ‖v‖) * ‖v‖ = c * ‖v‖ ^ 2 := by ring
            _ ≤ D * s := hqv
            _ ≤ D * ((g : ℝ) * ‖v‖ * ‖x‖) := mul_le_mul_of_nonneg_left hs hD
            _ = (D * g * ‖x‖) * ‖v‖ := by ring
        exact le_of_mul_le_mul_right this hpos
      calc c * s ≤ c * ((g : ℝ) * ‖v‖ * ‖x‖) := mul_le_mul_of_nonneg_left hs hc.le
        _ = (g : ℝ) * ‖x‖ * (c * ‖v‖) := by ring
        _ ≤ (g : ℝ) * ‖x‖ * (D * g * ‖x‖) := mul_le_mul_of_nonneg_left hcn (by positivity)
        _ = (g : ℝ) ^ 2 * D * ‖x‖ ^ 2 := by ring

theorem hermForm_isotropic_combination_norm_compare : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin g → Fin g → ℂ) (τ : Fin g → Fin g → ℂ) (c D Λ : ℝ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → 0 < c → (∀ v : Fin g → ℝ, c * ‖v‖ ^ 2 ≤ D * (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) → ‖τ‖ ≤ Λ → ∀ a : Fin g → ℂ, c * ‖a‖ ^ 2 ≤ D * ((g : ℝ) * Λ) ^ 2 * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (∑ k, a k • E k) (∑ k, a k • E k)).re ∧ c * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (∑ k, a k • E k) (∑ k, a k • E k)).re ≤ 2 * (g : ℝ) ^ 2 * D * ‖a‖ ^ 2 := by
  intro g Hm E F τ c D Λ hH hpos hF hA hFE hc hqτ hΛ z
  rcases Nat.eq_zero_or_pos g with hg0 | hg
  · subst hg0
    have hz : ‖z‖ = 0 := by rw [Subsingleton.elim z 0, norm_zero]
    rw [hz]
    simp [hermForm]
  have hexp : ∀ z w : Fin g → ℂ, hermForm Hm z w = ∑ x, ∑ y, z x * Hm x y * star (w y) := by
    intro z w; unfold hermForm; simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [Pi.star_apply]; ring
  have lin1 : ∀ (c : Fin g → ℂ) (w : Fin g → ℂ),
      hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
    intro c w
    unfold hermForm
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have symm : ∀ z w : Fin g → ℂ, hermForm Hm w z = star (hermForm Hm z w) := by
    intro z w
    simp only [hexp, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show star (Hm x y) = Hm y x from hH.apply y x]; ring
  have lin2 : ∀ (c : Fin g → ℂ) (z : Fin g → ℂ),
      hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
    intro c z
    rw [symm, lin1, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', ← symm]
  set a : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hA])
  have asymm : aᵀ = a := by
    ext i k; simp only [a, Matrix.transpose_apply, Matrix.of_apply]; rw [symm]; simp
  set Y : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i j => (τ i j).im with hY
  have hYA : Yᵀ * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hF j, lin1] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] at h
    simpa [Matrix.mul_apply, Matrix.one_apply, Y] using h
  have hAY : a * Y = 1 := by
    have h := congrArg Matrix.transpose hYA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, asymm, Matrix.transpose_one] at h
  have hYs : Yᵀ = Y := by
    calc Yᵀ = Yᵀ * (a * Y) := by rw [hAY, Matrix.mul_one]
    _ = (Yᵀ * a) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hYA, Matrix.one_mul]
  have hYA' : Y * a = 1 := by rw [← hYs]; exact hYA
  have him : ∀ v : Fin g → ℝ, (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im = v ⬝ᵥ (Y *ᵥ v) := by
    intro v
    simp only [Complex.im_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Y, Complex.mul_im]; ring
  have hq : ∀ v : Fin g → ℝ, c * ‖v‖ ^ 2 ≤ D * (v ⬝ᵥ (Y *ᵥ v)) := fun v => by
    rw [← him]; exact hqτ v
  have hD : 0 ≤ D := by
    set v1 : Fin g → ℝ := fun _ => 1
    have hv1 : v1 ≠ 0 := fun h => by simpa [v1] using congrFun h ⟨0, hg⟩
    have hp := ((GlobalTheory.riemann_relations_period_matrix g g Hm E F τ hH hpos hF hA hFE).1 v1 hv1)
    have h2 := hqτ v1
    by_contra hneg
    push_neg at hneg
    have : D * (∑ i, ∑ j, (v1 i : ℂ) * τ i j * (v1 j : ℂ)).im < 0 := mul_neg_of_neg_of_pos hneg hp
    have : 0 ≤ c * ‖v1‖ ^ 2 := by positivity
    linarith
  have hYb : ∀ i j, |Y i j| ≤ Λ := fun i j => by
    calc |Y i j| = |(τ i j).im| := by simp [Y]
      _ ≤ ‖τ i j‖ := Complex.abs_im_le_norm _
      _ ≤ ‖τ i‖ := norm_le_pi_norm (τ i) j
      _ ≤ ‖τ‖ := norm_le_pi_norm τ i
      _ ≤ Λ := hΛ
  set x : Fin g → ℝ := fun k => (z k).re with hx
  set y : Fin g → ℝ := fun k => (z k).im with hy
  have hre : (hermForm Hm (∑ k, z k • E k) (∑ k, z k • E k)).re
      = x ⬝ᵥ (a *ᵥ x) + y ⬝ᵥ (a *ᵥ y) := by
    rw [lin1]
    simp only [lin2, hAr, Complex.re_sum, dotProduct, Matrix.mulVec, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp [x, y, Complex.mul_re, Complex.mul_im]; ring
  have hxa : ‖x‖ ≤ ‖z‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k =>
    le_trans (b := ‖z k‖) (by simpa [x, Real.norm_eq_abs] using Complex.abs_re_le_norm (z k)) (norm_le_pi_norm z k)
  have hya : ‖y‖ ≤ ‖z‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k =>
    le_trans (b := ‖z k‖) (by simpa [y, Real.norm_eq_abs] using Complex.abs_im_le_norm (z k)) (norm_le_pi_norm z k)
  have hax : ‖z‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have hb : ‖z‖ ≤ Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => by
        have h1 : (x k) ^ 2 ≤ ‖x‖ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _)
            (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x k) 2
        have h2 : (y k) ^ 2 ≤ ‖y‖ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _)
            (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y k) 2
        have h3 : ‖z k‖ ^ 2 = (x k) ^ 2 + (y k) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; simp [x, y]; ring
        have := Real.abs_le_sqrt (x := ‖z k‖) (y := ‖x‖ ^ 2 + ‖y‖ ^ 2) (by rw [h3]; linarith)
        simpa using this
    calc ‖z‖ ^ 2 ≤ (Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨hx1, hx2⟩ := quadForm_inverse_compare a Y c D Λ hYA' hc hD hYb hq x
  obtain ⟨hy1, hy2⟩ := quadForm_inverse_compare a Y c D Λ hYA' hc hD hYb hq y
  rw [hre]
  constructor
  · calc c * ‖z‖ ^ 2 ≤ c * (‖x‖ ^ 2 + ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left hax hc.le
      _ = c * ‖x‖ ^ 2 + c * ‖y‖ ^ 2 := by ring
      _ ≤ D * ((g : ℝ) * Λ) ^ 2 * (x ⬝ᵥ (a *ᵥ x) + y ⬝ᵥ (a *ᵥ y)) := by linarith
  · have hK : 0 ≤ (g : ℝ) ^ 2 * D := by positivity
    have ex : ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxa 2
    have ey : ‖y‖ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hya 2
    have := mul_le_mul_of_nonneg_left ex hK
    have := mul_le_mul_of_nonneg_left ey hK
    calc c * (x ⬝ᵥ (a *ᵥ x) + y ⬝ᵥ (a *ᵥ y)) = c * (x ⬝ᵥ (a *ᵥ x)) + c * (y ⬝ᵥ (a *ᵥ y)) := by ring
      _ ≤ 2 * (g : ℝ) ^ 2 * D * ‖z‖ ^ 2 := by nlinarith

end GlobalTheory
