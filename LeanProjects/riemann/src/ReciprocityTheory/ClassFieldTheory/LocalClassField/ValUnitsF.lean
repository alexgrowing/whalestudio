import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsE

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem rpow_neg_div_nonneg (i : ℕ) : 0 ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

theorem rpow_neg_div_lt_one (he : 0 < eK p K) {i : ℕ} (hi : 0 < i) : (p : ℝ) ^ (- (i : ℝ) / eK p K) < 1 := by
  have he' : (0 : ℝ) < eK p K := by positivity
  have hi' : (0 : ℝ) < i := by positivity
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_p_real p) (div_neg_of_neg_of_pos (by linarith) he')

def UKi (i : ℕ) : Subgroup Kˣ where
  carrier := {x | x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K)}
  one_mem' := ⟨(UK p K).one_mem, by
    show ‖(((1 : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    simp only [Units.val_one, OneMemClass.coe_one, sub_self, norm_zero]
    exact rpow_neg_div_nonneg p K i⟩
  mul_mem' := fun {x y} hx hy => ⟨(UK p K).mul_mem hx.1 hy.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have h : (((x * y : Kˣ) : K) : PadicAlgCl p) - 1 =
        ((x : K) : PadicAlgCl p) * (((y : K) : PadicAlgCl p) - 1) + (((x : K) : PadicAlgCl p) - 1) := by
      rw [Units.val_mul, MulMemClass.coe_mul]; ring
    show ‖(((x * y : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h]
    refine (PadicAlgCl.isNonarchimedean p _ _).trans (max_le ?_ hx.2)
    rw [norm_mul, hx1, one_mul]; exact hy.2⟩
  inv_mem' := fun {x} hx => ⟨(UK p K).inv_mem hx.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have hx0 := coe_units_ne_zero x
    have h : (((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1 =
        - ((((x : K) : PadicAlgCl p) - 1) * ((x : K) : PadicAlgCl p)⁻¹) := by
      rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      field_simp
      ring
    show ‖(((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h, norm_neg, norm_mul, norm_inv, hx1, inv_one, mul_one]; exact hx.2⟩

theorem mem_UKi_iff (i : ℕ) (x : Kˣ) :
    x ∈ UKi p K i ↔ x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) := Iff.rfl

theorem norm_pow_uniformiser (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) :
    ‖((π : K) : PadicAlgCl p)‖ ^ i = (p : ℝ) ^ (- (i : ℝ) / eK p K) := by
  have h := norm_eq_rpow_vK p K hK (π ^ i)
  rw [vK_pow, hπ, mul_one, Int.cast_natCast, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, norm_pow] at h
  exact h

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
