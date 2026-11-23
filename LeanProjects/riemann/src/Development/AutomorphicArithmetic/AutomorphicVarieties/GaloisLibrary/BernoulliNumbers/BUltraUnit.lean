import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

private theorem b_ultra_int {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] {y : Ω}
    (h : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Ω)).integer y := h.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Ω))).mem_of_integral h1
  have h3 : ‖y‖₊ ≤ 1 := h2
  exact_mod_cast h3

private theorem b_ultra_unit {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) :
    ‖(m : Ω)‖ = 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).mpr hm
  have h1 : (a : Ω) * l + b * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hlt : ‖(l : Ω)‖ < 1 := by rw [hn]; exact inv_lt_one_of_one_lt₀ hl1
  refine le_antisymm (IsUltrametricDist.norm_intCast_le_one Ω m) ?_
  by_contra hc
  push Not at hc
  have ha := IsUltrametricDist.norm_intCast_le_one Ω a
  have hb := IsUltrametricDist.norm_intCast_le_one Ω b
  have h2 := IsUltrametricDist.norm_add_le_max ((a : Ω) * l) ((b : Ω) * m)
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have h3 : ‖(a : Ω)‖ * ‖(l : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right ha (norm_nonneg _) hlt
  have h4 : ‖(b : Ω)‖ * ‖(m : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) hc
  exact absurd h2 (not_le.mpr (max_lt h3 h4))

private theorem b_ultra_log {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (M : ℤ) (hM : M ≠ 0) :
    -Real.log ‖(M : Ω)‖ = (padicValInt l M : ℝ) * Real.log l := by
  obtain ⟨m, hm⟩ := padicValInt_dvd (p := l) M
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, hc⟩
    have : (l : ℤ) ^ (padicValInt l M + 1) ∣ M := ⟨c, by
      conv_lhs => rw [hm, hc]
      ring⟩
    rcases (padicValInt_dvd_iff _ _).mp this with h | h
    · exact hM h
    · omega
  have h1 : (M : Ω) = (l : Ω) ^ padicValInt l M * m := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hm
  rw [h1, norm_mul, b_ultra_unit l hn m hnd, mul_one, norm_pow, hn, Real.log_pow, Real.log_inv]
  ring

theorem UpperTheory.V.Bern.b_ultra :
    ∀ {Ω ι : Type} [NormedField Ω] [IsUltrametricDist Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime], ‖(l : Ω)‖ = (l : ℝ)⁻¹ → ∀ (S : Set ι) (x : ι → Ω) (D : ℕ) (M : ℤ), S.Finite → M ≠ 0 → (∀ i ∈ S, IsIntegral ℤ ((D : Ω) * x i)) → ∏ᶠ i ∈ S, (D : Ω) * x i = (M : Ω) → ∑ᶠ i ∈ S, max 0 (-Real.log ‖x i‖) ≤ (padicValInt l M : ℝ) * Real.log l := by
  intro Ω ι _ _ _ l _ hn S x D M hS hM hint hprod
  rw [finprod_mem_eq_finite_toFinset_prod _ hS] at hprod
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← b_ultra_log l hn M hM, ← hprod, norm_prod]
  have hM' : (M : Ω) ≠ 0 := by exact_mod_cast hM
  have hne : ∀ i ∈ hS.toFinset, (D : Ω) * x i ≠ 0 := by
    rw [← Finset.prod_ne_zero_iff, hprod]; exact hM'
  rw [Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (hne i hi)), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ∈ S := by simpa using hi
  have h0 := hne i hi
  have hD : (D : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hx : x i ≠ 0 := right_ne_zero_of_mul h0
  refine max_le ?_ ?_
  · have := Real.log_nonpos (norm_nonneg _) (b_ultra_int (hint i hi'))
    linarith
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hx)]
    have := Real.log_nonpos (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one Ω D)
    linarith
