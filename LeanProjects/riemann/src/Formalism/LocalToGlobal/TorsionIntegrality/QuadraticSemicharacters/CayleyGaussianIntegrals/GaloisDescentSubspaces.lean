import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero

noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory

namespace Formalism.L2.Th1.H

theorem exp_neg_le_factorial_div {s : ℝ} (hs : 0 < s) (n : ℕ) : Real.exp (-s) ≤ (n ! : ℝ) / s ^ n := by
  have h1 : s ^ n / (n ! : ℝ) ≤ Real.exp s := Real.pow_div_factorial_le_exp s hs.le n
  have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hp : 0 < s ^ n := pow_pos hs n
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos s) hp]
  rw [div_le_iff₀ hf] at h1
  linarith

theorem half_sq_sub_le {V : Type*} [NormedAddCommGroup V] (x z₀ : V) :
    ‖x‖ ^ 2 / 2 - ‖z₀‖ ^ 2 ≤ ‖x - z₀‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖x - z₀‖ + ‖z₀‖ := by
    simpa using norm_add_le (x - z₀) z₀
  have h0 := norm_nonneg x
  have h1 := norm_nonneg (x - z₀)
  have h2 := norm_nonneg z₀
  have h3 : ‖x‖ ^ 2 ≤ (‖x - z₀‖ + ‖z₀‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖x - z₀‖ - ‖z₀‖)]

theorem summable_gauss_of_discrete {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : AddSubgroup V) [hd : DiscreteTopology Λ] {a : ℝ} (ha : 0 < a) :
    Summable fun x : Λ => Real.exp (-a * ‖(x : V)‖ ^ 2) := by
  classical
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  have : DiscreteTopology L := hd
  set n : ℕ := Module.finrank ℤ L + 1 with hn
  have hsum : Summable fun z : L => ‖z‖⁻¹ ^ (2 * n) :=
    ZLattice.summable_norm_pow_inv L (2 * n) (by omega)
  have hsum' : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (2 * n) := hsum
  have hite : Summable fun x : Λ => if x = 0 then (1 : ℝ) else 0 := (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_)
    ((hsum'.mul_left ((n ! : ℝ) / a ^ n)).add hite)
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : 0 < ‖(x : V)‖ := by
      rw [norm_pos_iff]
      exact fun h => hx (Subtype.ext h)
    have hs : 0 < a * ‖(x : V)‖ ^ 2 := by positivity
    have h1 := exp_neg_le_factorial_div hs n
    rw [if_neg hx, add_zero]
    calc Real.exp (-a * ‖(x : V)‖ ^ 2) = Real.exp (-(a * ‖(x : V)‖ ^ 2)) := by rw [neg_mul]
      _ ≤ (n ! : ℝ) / (a * ‖(x : V)‖ ^ 2) ^ n := h1
      _ = (n ! : ℝ) / a ^ n * ‖(x : V)‖⁻¹ ^ (2 * n) := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp

theorem latticeGaussSummable : LatGaussSummable := by
  intro V _ _ _ Λ hΛ c r hc
  have : DiscreteTopology Λ := hΛ.1
  have hs : Summable fun x : Λ => Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2) :=
    summable_gauss_of_discrete Λ (by positivity)
  refine ⟨fun x => Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2), hs.mul_left _, ?_⟩
  intro x z₀ hz
  show _ ≤ Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := half_sq_sub_le (x : V) z₀
  have h2 : ‖z₀‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg z₀) hz 2
  nlinarith

theorem continuous_diag {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V) :
    Continuous fun z => H z z := by
  let b := Module.finBasis ℂ V
  have h : (fun z => H z z) = fun z => ∑ j, conj (b.coord j z) * H.flip (b j) z := by
    funext z
    have e : H z z = H z (∑ j, b.repr z j • b j) := by rw [b.sum_repr z]
    rw [e]
    simp only [map_sum, map_smulₛₗ, smul_eq_mul, LinearMap.flip_apply, Module.Basis.coord_apply]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_conj.comp (LinearMap.continuous_of_finiteDimensional (b.coord j))).mul
    (LinearMap.continuous_of_finiteDimensional (H.flip (b j)))

theorem exp_neg_sq_le_japanese {a : ℝ} (ha : 0 < a) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-a * t ^ 2) ≤ Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * (1 + t) ^ (-((2 * m : ℕ) : ℝ)) := by
  have hs : 0 < a * (1 + t ^ 2) := by positivity
  have h1 := exp_neg_le_factorial_div hs m
  have h2 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (1 - t)]
  have h3 : (1 + t) ^ (2 * m) ≤ 2 ^ m * (1 + t ^ 2) ^ m := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 m
  have h4 : 0 < (1 + t) ^ (2 * m) := by positivity
  have h5 : 0 < (1 + t ^ 2) ^ m := by positivity
  have ham : 0 < a ^ m := pow_pos ha m
  have hf : (0 : ℝ) < (m ! : ℝ) := by exact_mod_cast m.factorial_pos
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have e : -a * t ^ 2 = a + -(a * (1 + t ^ 2)) := by ring
  rw [e, Real.exp_add]
  have h6 : ((1 + t ^ 2) ^ m)⁻¹ ≤ 2 ^ m * ((1 + t) ^ (2 * m))⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h5 h4]
    linarith
  calc Real.exp a * Real.exp (-(a * (1 + t ^ 2)))
      ≤ Real.exp a * ((m ! : ℝ) / (a * (1 + t ^ 2)) ^ m) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
    _ = Real.exp a * (m ! : ℝ) / a ^ m * ((1 + t ^ 2) ^ m)⁻¹ := by
        rw [mul_pow]; field_simp
    _ ≤ Real.exp a * (m ! : ℝ) / a ^ m * (2 ^ m * ((1 + t) ^ (2 * m))⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * ((1 + t) ^ (2 * m))⁻¹ := by ring

theorem GaussIntegrable_of (h : FormNorm) : GaussIntegrable := by
  intro V _ _ _ _ _ μ _ H hH hP c hc
  obtain ⟨c₀, C, hc₀, _, hb⟩ := h V H hH hP
  have hcont : Continuous fun z => Real.exp (-c * (H z z).re) :=
    Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (continuous_diag H)))
  set m : ℕ := Module.finrank ℝ V + 1 with hm
  have hJ : Integrable (fun z : V => (1 + ‖z‖) ^ (-((2 * m : ℕ) : ℝ))) μ :=
    integrable_one_add_norm (by
      have : Module.finrank ℝ V < 2 * m := by omega
      exact_mod_cast this)
  have ha : 0 < c * c₀ := by positivity
  have hint : Integrable (fun z => Real.exp (-c * (H z z).re)) μ := by
    refine Integrable.mono' (hJ.const_mul (Real.exp (c * c₀) * (m ! : ℝ) * 2 ^ m / (c * c₀) ^ m))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_sq_le_japanese ha m (norm_nonneg z))
    have := (hb z).1
    nlinarith
  refine ⟨hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun z => Real.exp (-c * (H z z).re)) = Set.univ := by
    ext z
    simp [Real.exp_ne_zero]
  rw [hsupp]
  exact isOpen_univ.measure_pos μ Set.univ_nonempty

end Formalism.L2.Th1.H
