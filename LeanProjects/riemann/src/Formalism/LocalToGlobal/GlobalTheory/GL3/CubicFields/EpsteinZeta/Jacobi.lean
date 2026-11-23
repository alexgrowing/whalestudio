import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem jac_riemannZeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (show (3 : ℕ) ≠ 0 by norm_num)
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  have hb : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  rw [show (6 : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h, hb]
  norm_num [Nat.factorial]
  ring

theorem jac_mem_closure (a z w : ℂ) :
    w ∈ AddSubgroup.closure ({a, a * z} : Set ℂ) ↔ ∃ v : Fin 2 → ℤ, w = a * ((v 0 : ℂ) * z + v 1) := by
  rw [AddSubgroup.mem_closure_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨![n, m], ?_⟩
    simp [zsmul_eq_mul]
    ring
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, by simp [zsmul_eq_mul]; ring⟩

theorem jac_inj (z : ℂ) (hz : 0 < z.im) :
    Function.Injective (fun v : Fin 2 → ℤ => (v 0 : ℂ) * z + v 1) := by
  intro v w h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero] at him
  have h0r : ((v 0 : ℤ) : ℝ) = ((w 0 : ℤ) : ℝ) := mul_right_cancel₀ hz.ne' him
  have h0 : v 0 = w 0 := by exact_mod_cast h0r
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero] at hre
  rw [h0r] at hre
  have h1 : v 1 = w 1 := by
    have h2 : ((v 1 : ℤ) : ℝ) = ((w 1 : ℤ) : ℝ) := by linarith
    exact_mod_cast h2
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem jac_eisG (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) (k : ℕ) (hk : k ≠ 0) :
    eisG (AddSubgroup.closure {a, a * z}) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ,
        EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane) := by
  unfold eisG
  have hinj := jac_inj z hz
  let f : {v : Fin 2 → ℤ // v ≠ 0} → {w : ℂ // w ∈ AddSubgroup.closure ({a, a * z} : Set ℂ) ∧ w ≠ 0} :=
    fun v => ⟨a * ((v.1 0 : ℂ) * z + v.1 1), (jac_mem_closure a z _).mpr ⟨v.1, rfl⟩,
      mul_ne_zero ha (fun h => v.2 (hinj (by simpa using h)))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have h1 := congrArg Subtype.val h
      exact Subtype.ext (hinj (mul_left_cancel₀ ha h1))
    · rintro ⟨w, hw, hw0⟩
      obtain ⟨v, rfl⟩ := (jac_mem_closure a z w).mp hw
      refine ⟨⟨v, fun hv => hw0 (by simp [hv])⟩, rfl⟩
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  have hsupp : Function.support (fun v : Fin 2 → ℤ =>
      EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane)) ⊆ {v | v ≠ 0} := by
    intro v hv
    by_contra hv0
    simp only [Set.mem_setOf_eq, not_not] at hv0
    apply hv
    subst hv0
    have hk2 : ((2 * k : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : 2 * k ≠ 0)
    simp [EisensteinSeries.eisSummand]
    exact zero_zpow _ (by omega)
  rw [← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  simp only [Equiv.ofBijective_apply, f, EisensteinSeries.eisSummand, UpperHalfPlane.coe_mk, zpow_natCast]
  rw [mul_pow, one_div, mul_inv, zpow_neg, zpow_natCast]

theorem E4_eq_half_eisensteinSeries (z : UpperHalfPlane) :
    ModularForm.E₄ z = 1 / 2 * _root_.eisensteinSeries (N := 1) 0 (4 : ℕ) z := rfl

theorem E6_eq_half_eisensteinSeries (z : UpperHalfPlane) :
    ModularForm.E₆ z = 1 / 2 * _root_.eisensteinSeries (N := 1) 0 (6 : ℕ) z := rfl

theorem eisenstein_G4_closure (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    eisG (AddSubgroup.closure {a, a * z}) 2 =
      (a ^ 4)⁻¹ * (2 * ((Real.pi : ℂ) ^ 4 / 90) * ModularForm.E₄ (⟨z, hz⟩ : UpperHalfPlane)) := by
  rw [jac_eisG a z ha hz 2 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 4) (by norm_num) (⟨z, hz⟩ : UpperHalfPlane)
  rw [show ((2 * 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, h2, E4_eq_half_eisensteinSeries,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four, show a ^ (2 * 2) = a ^ 4 by norm_num]
  ring

theorem eisenstein_G6_closure (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    eisG (AddSubgroup.closure {a, a * z}) 3 =
      (a ^ 6)⁻¹ * (2 * ((Real.pi : ℂ) ^ 6 / 945) * ModularForm.E₆ (⟨z, hz⟩ : UpperHalfPlane)) := by
  rw [jac_eisG a z ha hz 3 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 6) (by norm_num) (⟨z, hz⟩ : UpperHalfPlane)
  rw [show ((2 * 3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num, h2, E6_eq_half_eisensteinSeries,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, jac_riemannZeta_six, show a ^ (2 * 3) = a ^ 6 by norm_num]
  ring

theorem jac_discr (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    discr (AddSubgroup.closure {a, a * z}) = (2 * Real.pi / a) ^ 12 * ModularForm.eta z ^ 24 := by
  have hD := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq (⟨z, hz⟩ : UpperHalfPlane)
  have hD' : ModularForm.discriminant (⟨z, hz⟩ : UpperHalfPlane) = ModularForm.eta z ^ 24 := rfl
  rw [hD'] at hD
  rw [discr, g2, g3, eisenstein_G4_closure a z ha hz, eisenstein_G6_closure a z ha hz, hD]
  field_simp
  ring

theorem discr_closure_pair (a b : ℂ) (hab : 0 < (b / a).im) :
    discr (AddSubgroup.closure {a, b}) = (2 * Real.pi / a) ^ 12 * ModularForm.eta (b / a) ^ 24 := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  have h := jac_discr a (b / a) ha hab
  rw [show a * (b / a) = b by field_simp] at h
  exact h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
