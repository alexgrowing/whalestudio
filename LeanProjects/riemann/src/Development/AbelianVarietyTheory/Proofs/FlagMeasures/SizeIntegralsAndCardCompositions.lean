import Mathlib

open MeasureTheory Finset

namespace GlobalTheory

theorem setIntegral_cube_prod (a : ℕ) (S : Set ℝ) (f : Fin a → ℝ → ℝ) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => S), ∏ i, f i (τ i) = ∏ i, ∫ t in S, f i t := by
  have hμ : (volume : Measure (Fin a → ℝ)).restrict (Set.pi Set.univ (fun _ : Fin a => S)) =
      Measure.pi (fun _ : Fin a => (volume : Measure ℝ).restrict S) := by
    rw [volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin a => (volume : Measure ℝ)) (fun _ => S)
  rw [hμ]
  exact integral_fintype_prod_eq_prod (ι := Fin a) f

theorem setIntegral_Icc_const_div (c lo : ℝ) (h0 : 0 < lo) (h1 : lo ≤ 1 / 2) :
    ∫ t in Set.Icc lo (1 / 2), c / t = c * Real.log (1 / (2 * lo)) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
  have hfun : (fun t : ℝ => c / t) = fun t => c * t⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos h0 hhalf]
  congr 2
  field_simp

private lemma setIntegral_Ioo_pow_mul_div_eq (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) =
      (c : ℝ) * ((1 / 2 : ℝ) ^ (c * m) / ((c * m : ℕ) : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k, c * m = k + 1 := ⟨c * m - 1, by have := Nat.mul_le_mul hc hm; omega⟩
  have hcongr : Set.EqOn (fun t : ℝ => t ^ (c * m) * ((c : ℝ) / t)) (fun t => (c : ℝ) * t ^ k)
      (Set.Ioo (0 : ℝ) (1 / 2)) := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht.1
    simp only
    rw [hk, pow_succ]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
    integral_pow, hk]
  push_cast
  ring

theorem setIntegral_Ioo_pow_mul_div (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    0 ≤ ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ∧
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ≤ 1 := by
  rw [setIntegral_Ioo_pow_mul_div_eq c m hm hc]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * m) := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ (c * m) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcm : ((c * m : ℕ) : ℝ) = (c : ℝ) * m := by push_cast; ring
  rw [hcm]
  have hden : (0 : ℝ) < (c : ℝ) * m := by positivity
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_one hden]
  calc (c : ℝ) * (1 / 2 : ℝ) ^ (c * m) ≤ (c : ℝ) * 1 := by gcongr
    _ ≤ (c : ℝ) * m := by gcongr

theorem sum_card_composition_lt (q : ℕ) :
    ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), composition_card, Nat.add_sub_cancel, pow_succ]
    omega

theorem sizeIntegrals_and_card_compositions :
    (∀ (a : ℕ) (c : Fin a → ℝ) (lo : ℝ), 0 < lo → lo ≤ 1 / 2 → (∀ i, 0 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc lo (1 / 2)), ∏ i, c i / τ i = ∏ i, c i * Real.log (1 / (2 * lo))) ∧ (∀ (a : ℕ) (c : Fin a → ℕ) (m : ℕ), 1 ≤ m → (∀ i, 1 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Ioo (0 : ℝ) (1 / 2)), ∏ i, τ i ^ (c i * m) * ((c i : ℝ) / τ i) ≤ 1) ∧ ∀ q : ℕ, ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  refine ⟨fun a c lo h0 h1 _ => ?_, fun a c m hm hc => ?_, sum_card_composition_lt⟩
  · refine (setIntegral_cube_prod a (Set.Icc lo (1 / 2)) (fun i t => c i / t)).trans ?_
    exact Finset.prod_congr rfl fun i _ => setIntegral_Icc_const_div (c i) lo h0 h1
  · refine (setIntegral_cube_prod a (Set.Ioo (0 : ℝ) (1 / 2))
      (fun i t => t ^ (c i * m) * ((c i : ℝ) / t))).trans_le ?_
    exact Finset.prod_le_one (fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).1)
      fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).2

end GlobalTheory
