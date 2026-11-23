import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.IntDvd

open IsDedekindDomain HeightOneSpectrum

theorem int_dvd_of_local (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) (c : ℤ)
    (h : ∀ v : AwayP p, ∃ y ∈ v.1.adicCompletionIntegers ℚ,
      algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ) = algebraMap ℚ (v.1.adicCompletion ℚ) ((n : ℤ) : ℚ) * y) :
    (n : ℤ) ∣ c := by
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp
  · obtain ⟨ℓ, hℓ, n₁, hn₁⟩ : ∃ ℓ, ℓ.Prime ∧ ∃ n₁, n = ℓ * n₁ :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    have hℓp : ℓ ≠ p := by
      intro he
      have h3 : ℓ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n₁, hn₁⟩ hc
      rw [he, Nat.coprime_self] at h3
      exact (Fact.out : p.Prime).one_lt.ne' h3
    let w : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ),
      by simp [hℓ.ne_zero]⟩
    have hw : w.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro he
      rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at he
      simp only [Int.natAbs_natCast] at he
      exact hℓp he
    let v : AwayP p := ⟨w, hw⟩
    have hval : ∀ c : ℤ, Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ)) = v.1.intValuation c := by
      intro c
      rw [← valuation_of_algebraMap (K := ℚ), ← valuedAdicCompletion_eq_valuation]
      rfl
    have hℓc : (ℓ : ℤ) ∣ c := by
      obtain ⟨y, hy, e⟩ := h v
      have hy' : Valued.v y ≤ 1 := (mem_adicCompletionIntegers ℤ ℚ v.1).1 hy
      have h1 : v.1.intValuation c ≤ v.1.intValuation (n : ℤ) := by
        rw [← hval, ← hval, e, map_mul]
        exact mul_le_of_le_one_right' hy'
      have h2 : v.1.intValuation (n : ℤ) < 1 :=
        (intValuation_lt_one_iff_mem _ _).2 (Ideal.mem_span_singleton.2 ⟨n₁, by rw [hn₁]; push_cast; ring⟩)
      exact Ideal.mem_span_singleton.1 ((intValuation_lt_one_iff_mem _ _).1 (lt_of_le_of_lt h1 h2))
    obtain ⟨c₁, rfl⟩ := hℓc
    have hn₁pos : 0 < n₁ := by
      rcases Nat.eq_zero_or_pos n₁ with h0 | h0
      · rw [h0, mul_zero] at hn₁; omega
      · exact h0
    have hlt : n₁ < n := by
      rw [hn₁]; exact lt_mul_left hn₁pos hℓ.one_lt
    have hc₁ : n₁.Coprime p := Nat.Coprime.coprime_dvd_left ⟨ℓ, by rw [hn₁, Nat.mul_comm]⟩ hc
    have hd : (n₁ : ℤ) ∣ c₁ := ih n₁ hlt hn₁pos hc₁ c₁ fun v' => by
      obtain ⟨y, hy, e⟩ := h v'
      refine ⟨y, hy, ?_⟩
      have hne : algebraMap ℚ (v'.1.adicCompletion ℚ) ((ℓ : ℤ) : ℚ) ≠ 0 :=
        (map_ne_zero _).2 (by exact_mod_cast hℓ.ne_zero)
      apply mul_left_cancel₀ hne
      rw [← map_mul, ← _root_.mul_assoc, ← map_mul, ← Int.cast_mul, ← Int.cast_mul, e, hn₁]
      push_cast
      ring
    rw [hn₁]
    push_cast
    exact mul_dvd_mul_left _ hd

theorem int_dvd_of_eq_mul_isIntAf : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p),
    IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  intro p _ n hn hc c a ha e
  refine int_dvd_of_local p n hn hc c fun v => ⟨AfP.eval v a, ha v, ?_⟩
  have e' := congrArg (AfP.eval v) e
  rw [(AfP.eval v).commutes, map_mul, map_natCast] at e'
  rw [e']
  simp

end GlobalTheory.LKGeo.IntDvd
