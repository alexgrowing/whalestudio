import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.WindowSums.AnnihilatorPolynomials.DistinctTerms

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open PowerSeries

theorem ramified_valuation_inequality : RamifiedValuationInequality := by
  intro O _ _ _ ℓ hℓ ϖ e hϖ he hass ε u hε hu b y t hb hby hmem
  have hℓpos : 0 < ℓ := hℓ.out.pos
  obtain ⟨v₀, hv₀⟩ := hass

  have hℓnu : ¬ IsUnit (ℓ : O) := by
    intro h
    have h1 : IsUnit (ϖ ^ e) := by rw [← hv₀]; exact h.mul v₀.isUnit
    exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp h1)

  have hpow : ∀ k : ℕ, (ℓ : O) ^ k = ((v₀⁻¹ : Oˣ) : O) ^ k * ϖ ^ (e * k) := by
    intro k
    have : (ℓ : O) = ((v₀⁻¹ : Oˣ) : O) * ϖ ^ e := by
      rw [← hv₀, mul_comm (ℓ : O), ← mul_assoc, Units.inv_mul, one_mul]
    rw [this, mul_pow, ← pow_mul]

  set i₀ := (b - 1) / ℓ with hi₀def
  have h1 : ℓ * i₀ ≤ b - 1 := Nat.mul_div_le (b - 1) ℓ
  have h2 : b - 1 < ℓ * (i₀ + 1) := Nat.lt_mul_div_succ (b - 1) hℓpos
  have hi₀b : ℓ * i₀ < b := by omega
  have hbi : b ≤ ℓ * (i₀ + 1) := by omega
  have hyb : b ≤ ℓ * y := by
    have : (b : ℝ) ≤ (ℓ : ℝ) * (y : ℝ) := by
      rw [div_le_iff₀ (by exact_mod_cast hℓpos)] at hby; linarith
    exact_mod_cast this
  have hi₀y : i₀ < y := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hi₀b hyb)

  let vv : ℕ → ℕ := fun i => (y.choose i).factorization ℓ
  let mm : ℕ → ℕ := fun i => ordCompl[ℓ] (y.choose i)
  have hmmU : ∀ i ∈ Finset.range (y + 1), IsUnit ((mm i : ℕ) : O) := by
    intro i hi
    have hle : i ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcop : Nat.Coprime ℓ (mm i) := Nat.coprime_ordCompl hℓ.out (Nat.choose_pos hle).ne'
    have hic : IsCoprime (ℓ : ℤ) (mm i : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, c, hac⟩ := hic
    have hac' : (a : O) * ℓ + (c : O) * (mm i : O) = 1 := by
      have := congrArg (Int.cast : ℤ → O) hac
      push_cast at this
      exact this
    have : IsUnit ((a : O) * ℓ + (c : O) * (mm i : O)) := by rw [hac']; exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) hℓnu
    · exact isUnit_of_mul_isUnit_right h
  let mexp : ℕ → ℕ := fun i => vv i + (y - i)
  let w : ℕ → PowerSeries O := fun i =>
    C ((mm i : ℕ) : O) * ε ^ (y - i) * u ^ i * C (((v₀⁻¹ : Oˣ) : O) ^ mexp i)
  let ee : ℕ → ℕ := fun i => ℓ * i
  let ms : ℕ → ℕ := fun i => e * mexp i
  have hsum : (Formalism.WindowSums.p1 ℓ ε u) ^ y =
      ∑ i ∈ Finset.range (y + 1), w i * X ^ ee i * C (ϖ ^ ms i) := by
    unfold Formalism.WindowSums.p1
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hn : ((y.choose i : ℕ) : PowerSeries O) = C (ℓ : O) ^ vv i * C ((mm i : ℕ) : O) := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (y.choose i) ℓ]
      rw [Nat.cast_mul, Nat.cast_pow, ← map_natCast (C (R := O)) ℓ,
        ← map_natCast (C (R := O)) (mm i)]
    have hC : C (ℓ : O) ^ vv i * C (ℓ : O) ^ (y - i) =
        C (((v₀⁻¹ : Oˣ) : O) ^ mexp i) * C (ϖ ^ ms i) := by
      rw [← pow_add, ← map_pow, ← map_mul, ← hpow]
    have : (u * X ^ ℓ) ^ i * (C (ℓ : O) * ε) ^ (y - i) * ((y.choose i : ℕ) : PowerSeries O)
        = (C (ℓ : O) ^ vv i * C (ℓ : O) ^ (y - i)) * (C ((mm i : ℕ) : O) * ε ^ (y - i) * u ^ i)
          * X ^ (ℓ * i) := by
      rw [hn, mul_pow, mul_pow, ← pow_mul]; ring
    rw [this, hC]
    simp only [w, ee]
    ring
  have hw : ∀ i ∈ Finset.range (y + 1), IsUnit (w i) := fun i hi =>
    ((((hmmU i hi).map C).mul (hε.pow _)).mul (hu.pow _)).mul
      (((v₀⁻¹).isUnit.pow _).map C)
  have hinj : Set.InjOn ee (Finset.range (y + 1) : Set ℕ) := fun a _ c _ h =>
    Nat.eq_of_mul_eq_mul_left hℓpos h
  have hmem' : (∑ i ∈ Finset.range (y + 1), w i * X ^ ee i * C (ϖ ^ ms i)) ∈
      Ideal.span {(X : PowerSeries O) ^ b, C (ϖ ^ t)} := by
    rw [← hsum, Set.pair_comm]; exact hmem
  have hterm := (Formalism.WindowSums.mem_span_iff_of_distinct_exponents O ϖ hϖ.ne_zero hϖ.not_isUnit (Finset.range (y + 1))
    w ee ms b t hw hinj).1 hmem' i₀ (Finset.mem_range.2 (by omega))
  have htm : t ≤ e * (vv i₀ + (y - i₀)) := by
    rcases hterm with h | h
    · exact absurd h (by simp only [ee]; omega)
    · exact h
  have hv : vv i₀ ≤ Nat.log ℓ y := Nat.factorization_choose_le_log
  have hlog : ((Nat.log ℓ y : ℕ) : ℝ) ≤ Real.logb ℓ y := Real.natLog_le_logb y ℓ
  have hbl : (b : ℝ) / (ℓ : ℝ) ≤ (i₀ : ℝ) + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hℓpos)]
    exact_mod_cast (by linarith [hbi] : b ≤ (i₀ + 1) * ℓ)
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hte : (t : ℝ) / (e : ℝ) ≤ ((vv i₀ + (y - i₀) : ℕ) : ℝ) := by
    rw [div_le_iff₀ hepos]
    have : (t : ℝ) ≤ ((e * (vv i₀ + (y - i₀)) : ℕ) : ℝ) := by exact_mod_cast htm
    rw [Nat.cast_mul] at this
    linarith
  rw [Nat.cast_add, Nat.cast_sub hi₀y.le] at hte
  have hvR : (vv i₀ : ℝ) ≤ (Nat.log ℓ y : ℝ) := by exact_mod_cast hv
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
