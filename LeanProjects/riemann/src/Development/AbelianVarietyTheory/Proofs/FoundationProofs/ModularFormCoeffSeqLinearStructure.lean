import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.Lin

theorem norm_term (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = (Real.exp (-2 * π * τ.im)) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summ_norm (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r := Real.exp (-2 * π * τ.im) with hr
  have r0 : 0 < r := Real.exp_pos _
  have r1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := τ.im_pos
    have := Real.pi_pos
    nlinarith
  have hs : Summable fun n : ℕ => ((n : ℝ)) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos r0]; exact r1)
  have hs1 : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable fun n : ℕ => C * (((n : ℝ) + 1) ^ A * r ^ n) := by
    apply Summable.mul_left
    have := hs1.mul_right r⁻¹
    refine this.congr (fun n => ?_)
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs2
  rw [norm_mul, norm_term, ← hr, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg r0.le _)

theorem summ (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
  (summ_norm a ha τ).of_norm

theorem polyB_zero : PolyB (0 : ℕ → ℂ) := ⟨0, 0, fun n => by simp⟩

theorem polyB_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (a + b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨D, B, hD⟩ := hb
  refine ⟨|C| + |D|, A + B, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have hA : ((n : ℝ) + 1) ^ A ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have hB : ((n : ℝ) + 1) ^ B ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have p0 : 0 ≤ ((n : ℝ) + 1) ^ A := by positivity
  have p1 : 0 ≤ ((n : ℝ) + 1) ^ B := by positivity
  calc ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ C * ((n : ℝ) + 1) ^ A + D * ((n : ℝ) + 1) ^ B := add_le_add (hC n) (hD n)
    _ ≤ |C| * ((n : ℝ) + 1) ^ (A + B) + |D| * ((n : ℝ) + 1) ^ (A + B) := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) p0).trans
            (mul_le_mul_of_nonneg_left hA (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self D) p1).trans
            (mul_le_mul_of_nonneg_left hB (abs_nonneg D))
    _ = (|C| + |D|) * ((n : ℝ) + 1) ^ (A + B) := by ring

theorem polyB_smul (c : ℂ) (a : ℕ → ℂ) (ha : PolyB a) : PolyB (c • a) := by
  obtain ⟨C, A, hC⟩ := ha
  refine ⟨‖c‖ * C, A, fun n => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg c)

theorem qs_zero : qs (0 : ℕ → ℂ) = 0 := by
  funext τ; simp [qs]

theorem qs_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : qs (a + b) = qs a + qs b := by
  funext τ
  simp only [qs, Pi.add_apply, add_mul]
  exact (summ a ha τ).tsum_add (summ b hb τ)

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (c • a) = c • qs a := by
  funext τ
  simp only [qs, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem coprime_of_level (L : ℕ) (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) : IsCoprime (γ 1 1) (L : ℤ) := by
  obtain ⟨m, hm⟩ := h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨γ 0 0, -(γ 0 1 * m), ?_⟩
  rw [hm] at hdet
  linear_combination hdet

end GlobalTheory.EisM.Lin

open GlobalTheory.EisM.Lin in
theorem GlobalTheory.EisM.mf_linear : ∀ (k L : ℕ) (χ : ℤ → ℂ), (MF k L χ 0) ∧ (∀ a b, MF k L χ a → MF k L χ b → MF k L χ (a + b) ∧ qs (a + b) = qs a + qs b) ∧ (∀ (c : ℂ) a, MF k L χ a → MF k L χ (c • a) ∧ qs (c • a) = c • qs a) ∧ (∀ χ' a, (∀ d : ℤ, IsCoprime d L → χ d = χ' d) → MF k L χ a → MF k L χ' a) ∧ (∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a) ∧ (∀ L' a, L ∣ L' → CF k L χ a → CF k L' χ a) := by
  intro k L χ
  have lev : ∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a := by
    intro L' a hL ⟨hp, hi⟩
    refine ⟨hp, fun γ hγ τ => hi γ ?_ τ⟩
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hL) hγ
  refine ⟨⟨polyB_zero, fun γ _ τ => by simp [qs_zero]⟩, ?_, ?_, ?_, lev, ?_⟩
  · intro a b ⟨ha, ia⟩ ⟨hb, ib⟩
    have e := qs_add a b ha hb
    refine ⟨⟨polyB_add a b ha hb, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.add_apply, Pi.add_apply, ia γ hγ τ, ib γ hγ τ]
    ring
  · intro c a ⟨ha, ia⟩
    have e := qs_smul c a
    refine ⟨⟨polyB_smul c a ha, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ia γ hγ τ]
    ring
  · intro χ' a hχ ⟨ha, ia⟩
    refine ⟨ha, fun γ hγ τ => ?_⟩
    rw [ia γ hγ τ, hχ _ (coprime_of_level L γ hγ)]
  · intro L' a hL ⟨hm, hc⟩
    exact ⟨lev L' a hL hm, hc⟩
