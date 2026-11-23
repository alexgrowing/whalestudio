import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.MajSum

lemma summable_one_add_abs_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ s)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hs) ?_
  have hcof : ({0} : Set ℤ)ᶜ ∈ cofinite := (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  have hev : ∀ᶠ m : ℤ in cofinite, ‖((1 + |(m : ℝ)|) ^ s)⁻¹‖ ≤ |(m : ℝ)| ^ (-s) := by
    filter_upwards [hcof] with m hm
    have hm' : m ≠ 0 := by simpa using hm
    have hm0 : 0 < |(m : ℝ)| := abs_pos.2 (by exact_mod_cast hm')
    have hpos : 0 < 1 + |(m : ℝ)| := by linarith
    rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.rpow_nonneg hpos.le s)), Real.rpow_neg hm0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hm0 s)
      (Real.rpow_le_rpow hm0.le (by linarith) (by linarith))
  simpa [Filter.eventually_cofinite] using hev

lemma term_le {x y z c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hc : 1 ≤ c) :
    ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2)⁻¹ ≤
      c ^ 5 * (((1 + x) ^ (3 / 2 : ℝ))⁻¹ * (((1 + y) ^ (3 / 2 : ℝ))⁻¹ * ((1 + z) ^ (2 : ℝ))⁻¹)) := by
  have hc0 : 0 < c := by linarith
  have hX : 0 < 1 + x := by linarith
  have hY : 0 < 1 + y := by linarith
  have hZ : 0 < 1 + z := by linarith
  have hS : 0 < 1 + x + y := by linarith
  have h1 : (1 + x) ^ (3 / 2 : ℝ) * (1 + y) ^ (3 / 2 : ℝ) ≤ (1 + x + y) ^ 3 := by
    rw [← Real.mul_rpow hX.le hY.le]
    have hle : (1 + x) * (1 + y) ≤ (1 + x + y) ^ 2 := by nlinarith [mul_nonneg hx hy]
    calc ((1 + x) * (1 + y)) ^ (3 / 2 : ℝ)
        ≤ ((1 + x + y) ^ 2) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (1 + x + y) ^ 3 := by
          rw [← Real.rpow_natCast (1 + x + y) 2, ← Real.rpow_mul hS.le,
            ← Real.rpow_natCast (1 + x + y) 3]
          norm_num
  have h2 : 1 + x + y ≤ c * (1 + x / c + y / c) := by
    have : c * (1 + x / c + y / c) = c + x + y := by field_simp
    rw [this]; linarith
  have h3 : 1 + z ≤ c * (1 + z / c) := by
    have : c * (1 + z / c) = c + z := by field_simp
    rw [this]; linarith
  have hP : 0 < 1 + x / c + y / c := by positivity
  have hQ : 0 < 1 + z / c := by positivity
  have h4 : (1 + x + y) ^ 3 ≤ (c * (1 + x / c + y / c)) ^ 3 :=
    pow_le_pow_left₀ hS.le h2 3
  have h5 : (1 + z) ^ 2 ≤ (c * (1 + z / c)) ^ 2 := pow_le_pow_left₀ hZ.le h3 2
  have hA : 0 < (1 + x) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  have hB : 0 < (1 + y) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hY _
  have hC : 0 < (1 + z) ^ (2 : ℝ) := Real.rpow_pos_of_pos hZ _
  have hC' : (1 + z) ^ (2 : ℝ) = (1 + z) ^ 2 := by
    rw [← Real.rpow_natCast (1 + z) 2]; norm_num
  have key : (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)) ≤
      c ^ 5 * ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2) := by
    rw [hC', ← mul_assoc]
    calc (1 + x) ^ (3 / 2 : ℝ) * (1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ 2
        ≤ (c * (1 + x / c + y / c)) ^ 3 * (c * (1 + z / c)) ^ 2 :=
          mul_le_mul (h1.trans h4) h5 (by positivity) (by positivity)
      _ = c ^ 5 * ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2) := by ring
  have hD : 0 < (1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2 := by positivity
  have hE : 0 < (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)) := by
    positivity
  have hinv : ((1 + x) ^ (3 / 2 : ℝ))⁻¹ * (((1 + y) ^ (3 / 2 : ℝ))⁻¹ * ((1 + z) ^ (2 : ℝ))⁻¹) =
      ((1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)))⁻¹ := by
    rw [mul_inv, mul_inv]
  rw [hinv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hD hE]
  linarith

lemma exists_int_of_den_eq_one {M : ℕ} (hM : 0 < M) {q : ℚ} (h : ((M : ℚ) * q).den = 1) :
    ∃ m : ℤ, (m : ℚ) / M = q := by
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨((M : ℚ) * q).num, ?_⟩
  rw [Rat.coe_int_num_of_den_eq_one h]
  field_simp

theorem summable_lattice_majorant :
    ∀ M : ℕ, 0 < M → Summable (fun p : ℚ × ℚ × ℚ =>
      if ((M : ℚ) * p.1).den = 1 ∧ ((M : ℚ) * p.2.1).den = 1 ∧ ((M : ℚ) * p.2.2).den = 1 then
        ((1 + |(p.1 : ℝ)| + |(p.2.1 : ℝ)|) ^ 3 * (1 + |(p.2.2 : ℝ)|) ^ 2)⁻¹ else (0 : ℝ)) := by
  intro M hM
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let g : ℤ × ℤ × ℤ → ℚ × ℚ × ℚ :=
    fun t => ((t.1 : ℚ) / M, (t.2.1 : ℚ) / M, (t.2.2 : ℚ) / M)
  have hdiv : ∀ a b : ℤ, (a : ℚ) / M = (b : ℚ) / M → a = b := by
    intro a b hab
    have : (a : ℚ) = b := by
      field_simp at hab
      exact hab
    exact_mod_cast this
  have hg : Function.Injective g := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [hdiv _ _ h1, hdiv _ _ h2, hdiv _ _ h3]
  have hden : ∀ a : ℤ, ((M : ℚ) * ((a : ℚ) / M)).den = 1 := by
    intro a
    rw [mul_div_cancel₀ _ hM0]
    exact Rat.den_intCast a
  refine (hg.summable_iff ?_).1 ?_
  · rintro ⟨p, q, r⟩ hx
    refine if_neg ?_
    rintro ⟨h1, h2, h3⟩
    obtain ⟨a, rfl⟩ := exists_int_of_den_eq_one hM h1
    obtain ⟨b, rfl⟩ := exists_int_of_den_eq_one hM h2
    obtain ⟨c, rfl⟩ := exists_int_of_den_eq_one hM h3
    exact hx ⟨(a, b, c), rfl⟩
  · have hA := summable_one_add_abs_rpow (s := 3 / 2) (by norm_num)
    have hC := summable_one_add_abs_rpow (s := 2) (by norm_num)
    have hnA : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := fun m => by
      positivity
    have hnC : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (2 : ℝ))⁻¹ := fun m => by
      positivity
    have hBC := hA.mul_of_nonneg hC hnA hnC
    have hnBC : 0 ≤ fun t : ℤ × ℤ =>
        ((1 + |(t.1 : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ * ((1 + |(t.2 : ℝ)|) ^ (2 : ℝ))⁻¹ := fun t => by
      positivity
    have hABC := (hA.mul_of_nonneg hBC hnA hnBC).mul_left ((M : ℝ) ^ 5)
    refine Summable.of_nonneg_of_le ?_ ?_ hABC
    · rintro ⟨a, b, c⟩
      simp only [Function.comp, g]
      split_ifs <;> positivity
    · rintro ⟨a, b, c⟩
      simp only [Function.comp, g]
      rw [if_pos ⟨hden a, hden b, hden c⟩]
      have hcast : ∀ u : ℤ, |(((u : ℚ) / M : ℚ) : ℝ)| = |(u : ℝ)| / M := by
        intro u
        push_cast
        rw [abs_div, Nat.abs_cast]
      rw [hcast a, hcast b, hcast c]
      exact term_le (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hMR

end GlobalTheory.CompanionTheory.MajSum
