import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem modGrowth_pow_bounds (y : ℝ) (hy : 0 < y) (A : ℕ) :
    max y y⁻¹ ^ A ≤ y ^ A + (y ^ A)⁻¹ ∧ y ^ A + (y ^ A)⁻¹ ≤ 2 * max y y⁻¹ ^ A := by
  rw [← inv_pow]
  have h1 : 0 < y ^ A := pow_pos hy A
  have h2 : 0 < y⁻¹ ^ A := pow_pos (inv_pos.mpr hy) A
  rcases le_total y y⁻¹ with h | h
  · rw [max_eq_right h]
    have : y ^ A ≤ y⁻¹ ^ A := pow_le_pow_left₀ hy.le h A
    constructor <;> linarith
  · rw [max_eq_left h]
    have : y⁻¹ ^ A ≤ y ^ A := pow_le_pow_left₀ (inv_pos.mpr hy).le h A
    constructor <;> linarith

theorem one_le_max_inv (y : ℝ) (hy : 0 < y) : 1 ≤ max y y⁻¹ := by
  rcases le_total 1 y with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hy).mpr h)

theorem mod_of_bound (F : ℍ → ℂ) (C : ℝ) (A : ℕ) (h : ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A) :
    Mod F := by
  refine ⟨max C 0, A, fun τ => ?_⟩
  obtain ⟨b1, _⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hM : 0 ≤ max τ.im τ.im⁻¹ ^ A :=
    pow_nonneg (le_trans zero_le_one (one_le_max_inv _ τ.im_pos)) A
  calc ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := h τ
    _ ≤ max C 0 * max τ.im τ.im⁻¹ ^ A := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 (le_max_right _ _)

theorem bound_of_mod (F : ℍ → ℂ) (hF : Mod F) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := by
  obtain ⟨C, A, h⟩ := hF
  refine ⟨2 * max C 0, A, by positivity, fun τ => ?_⟩
  obtain ⟨_, b2⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hh : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ :=
    add_nonneg (pow_pos τ.im_pos A).le (inv_pos.mpr (pow_pos τ.im_pos A)).le
  calc ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := h τ
    _ ≤ max C 0 * (τ.im ^ A + (τ.im ^ A)⁻¹) := mul_le_mul_of_nonneg_right (le_max_left _ _) hh
    _ ≤ max C 0 * (2 * max τ.im τ.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left b2 (le_max_right _ _)
    _ = _ := by ring

theorem mod_add (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ + G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C + D) (A + B) fun τ => ?_
  have hM := one_le_max_inv _ τ.im_pos
  have eA : max τ.im τ.im⁻¹ ^ A ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_right A B)
  have eB : max τ.im τ.im⁻¹ ^ B ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_left B A)
  calc ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le _ _
    _ ≤ C * max τ.im τ.im⁻¹ ^ A + D * max τ.im τ.im⁻¹ ^ B := add_le_add (h1 τ) (h2 τ)
    _ ≤ C * max τ.im τ.im⁻¹ ^ (A + B) + D * max τ.im τ.im⁻¹ ^ (A + B) :=
        add_le_add (mul_le_mul_of_nonneg_left eA hC) (mul_le_mul_of_nonneg_left eB hD)
    _ = _ := by ring

theorem mod_mul (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ * G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C * D) (A + B) fun τ => ?_
  have hM := le_trans zero_le_one (one_le_max_inv _ τ.im_pos)
  calc ‖F τ * G τ‖ = ‖F τ‖ * ‖G τ‖ := norm_mul _ _
    _ ≤ (C * max τ.im τ.im⁻¹ ^ A) * (D * max τ.im τ.im⁻¹ ^ B) :=
        mul_le_mul (h1 τ) (h2 τ) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hM A))
    _ = _ := by ring

theorem mod_const (c : ℂ) : Mod fun _ => c :=
  mod_of_bound _ ‖c‖ 0 fun τ => by simp

theorem im_slz_arg (δ : M2) (hc : δ 1 0 = 0) (τ : ℍ) :
    (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im
      = (δ 0 0 : ℝ) / (δ 1 1 : ℝ) * τ.im := by
  rw [hc]
  simp [Complex.div_im]
  rcases eq_or_ne ((δ 1 1 : ℤ) : ℝ) 0 with h | h
  · simp [h]
  · field_simp

theorem max_inv_mul_le (r y : ℝ) (hr : 0 < r) (hy : 0 < y) :
    max (r * y) (r * y)⁻¹ ≤ max r r⁻¹ * max y y⁻¹ := by
  have h1 := one_le_max_inv r hr
  have h2 := one_le_max_inv y hy
  rw [mul_inv]
  apply max_le
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) hy.le (by linarith)
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_pos.mpr hy).le (by linarith)

theorem mod_slz (F : ℍ → ℂ) (k : ℕ) (δ : M2) (hdet : 0 < δ.det) (hc : δ 1 0 = 0) (hF : Mod F) :
    Mod (slz k δ F) := by
  obtain ⟨C, A, hC0, hC⟩ := bound_of_mod F hF
  have hdet' : δ.det = δ 0 0 * δ 1 1 := by rw [Matrix.det_fin_two, hc]; ring
  have had : (0 : ℝ) < (δ 0 0 : ℝ) * (δ 1 1 : ℝ) := by
    have : (0 : ℤ) < δ 0 0 * δ 1 1 := hdet' ▸ hdet
    exact_mod_cast this
  have hd : (δ 1 1 : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at had; exact lt_irrefl _ had
  have hrpos : (0 : ℝ) < (δ 0 0 : ℝ) / (δ 1 1 : ℝ) := by
    have : (δ 0 0 : ℝ) / (δ 1 1 : ℝ) = (δ 0 0 : ℝ) * δ 1 1 / ((δ 1 1 : ℝ) ^ 2) := by
      field_simp
    rw [this]; exact div_pos had (by positivity)
  set r : ℝ := (δ 0 0 : ℝ) / (δ 1 1 : ℝ) with hr
  set K : ℝ := ‖((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹‖ with hK
  set R : ℝ := max r r⁻¹ with hR
  have hR1 : 1 ≤ R := one_le_max_inv r hrpos
  refine mod_of_bound _ (K * (C * R ^ A)) A fun τ => ?_
  have him := im_slz_arg δ hc τ
  rw [← hr] at him
  have hz : 0 < (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im := by
    rw [him]; exact mul_pos hrpos τ.im_pos
  set w : ℍ := ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))) with hw
  have hwim : w.im = r * τ.im := by
    rw [hw, ofComplex_apply_of_im_pos hz]; exact him
  have hMw : max w.im w.im⁻¹ ^ A ≤ R ^ A * max τ.im τ.im⁻¹ ^ A := by
    rw [← mul_pow, hwim]
    exact pow_le_pow_left₀ (le_trans zero_le_one (one_le_max_inv _ (mul_pos hrpos τ.im_pos)))
      (max_inv_mul_le r τ.im hrpos τ.im_pos) A
  have hslz : slz k δ F τ = (((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) * F w := by
    rw [slz, hw]; simp [hc]
  rw [hslz, norm_mul, ← hK]
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * ‖F w‖ ≤ K * (C * max w.im w.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left (hC w) hK0
    _ ≤ K * (C * (R ^ A * max τ.im τ.im⁻¹ ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMw hC0) hK0
    _ = _ := by ring

theorem mod_algebra : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) :=
  ⟨fun F G hF hG => ⟨mod_add F G hF hG, mod_mul F G hF hG⟩, mod_const,
    fun F k δ hdet hc hF => mod_slz F k δ hdet hc hF⟩

end GlobalTheory.EisM
