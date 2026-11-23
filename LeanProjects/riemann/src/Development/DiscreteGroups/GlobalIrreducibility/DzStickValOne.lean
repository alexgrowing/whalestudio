import Development.DiscreteGroups.GlobalIrreducibility.DzStickValBasic

noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

theorem sum_inv_mul_trace (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Fintype k]
    [Algebra (ZMod p) k] :
    ∑ x : k, x⁻¹ * algebraMap (ZMod p) k (Algebra.trace (ZMod p) k x) = -1 := by
  classical
  have hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := k), ZMod.card]
  have hn : 0 < Module.finrank (ZMod p) k := Module.finrank_pos
  simp_rw [FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_zmod, Finset.mul_sum]
  rw [Finset.sum_comm]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [hm, Finset.sum_range_succ']
  have h0 : ∑ x : k, x⁻¹ * x ^ p ^ 0 = -1 := by
    have h1 : ∀ x : k, x⁻¹ * x ^ p ^ 0 = 1 - if x = 0 then 1 else 0 := by
      intro x
      by_cases hx : x = 0 <;> simp [hx]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib]
    simp
  rw [h0, Finset.sum_eq_zero, zero_add]
  intro i hi
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpos : 1 < p ^ (i + 1) := Nat.one_lt_pow (by omega) hp1
  have h2 : ∀ x : k, x⁻¹ * x ^ p ^ (i + 1) = x ^ (p ^ (i + 1) - 1) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [inv_zero, zero_mul, zero_pow (by omega)]
    · rw [pow_sub₀ _ hx hpos.le, pow_one, mul_comm]
  simp_rw [h2]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hcard, hm, Nat.succ_eq_add_one]
  have h3 : p ^ (i + 1) < p ^ (m + 1) :=
    Nat.pow_lt_pow_right hp1 (by simpa using hi)
  omega

theorem exists_pow_eq_one_add {A : Type*} [CommRing A] (ζ : A) (n : ℕ) :
    ∃ r : A, ζ ^ n = 1 + n * (ζ - 1) + (ζ - 1) ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r * ζ + n, ?_⟩
    rw [pow_succ, hr]
    push_cast
    ring

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

theorem sum_inv_val_add_one_mem :
    (∑ x : k, (D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) + 1 ∈ Q.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_sum, map_one]
  have h : ∀ x : k, Ideal.Quotient.mk Q.asIdeal
      ((D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) =
      D.ι (x⁻¹ * algebraMap (ZMod p) k (Algebra.trace (ZMod p) k x)) := by
    intro x
    rw [map_mul, map_mul, MulChar.inv_apply', D.mk_ω, map_natCast]
    congr 1
    conv_rhs => rw [← ZMod.natCast_zmod_val (Algebra.trace (ZMod p) k x)]
    rw [map_natCast, map_natCast]
  simp_rw [h]
  rw [← map_sum, sum_inv_mul_trace, map_neg, map_one, neg_add_cancel]

theorem exists_g_one_eq (h : 1 < p ^ f - 1) :
    ∃ y ∈ Q.asIdeal, D.g 1 = (D.ζ - 1) * (-1 + y) := by
  choose r hr using fun x : k => exists_pow_eq_one_add D.ζ (Algebra.trace (ZMod p) k x).val
  have hne : D.ω⁻¹ ≠ 1 := by
    intro h1
    apply D.ω_pow_ne_one one_pos h
    rw [pow_one]
    exact inv_eq_one.mp h1
  have hs : ∑ x : k, (D.ω⁻¹) x = 0 := MulChar.sum_eq_zero_of_ne_one hne
  refine ⟨((∑ x : k, (D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) + 1) +
    (D.ζ - 1) * ∑ x : k, (D.ω⁻¹) x * r x, ?_, ?_⟩
  · exact Q.asIdeal.add_mem D.sum_inv_val_add_one_mem
      (Q.asIdeal.mul_mem_right _ D.ζ_sub_one_mem)
  · have hg : D.g 1 = ∑ x : k, ((D.ω⁻¹) x +
        (D.ζ - 1) * ((D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) +
        (D.ζ - 1) * ((D.ζ - 1) * ((D.ω⁻¹) x * r x))) := by
      unfold GSDatum.g gaussSum
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pow_one]
      change _ * psi p k D.ζ D.prim.pow_eq_one x = _
      rw [psi_apply, hr x]
      ring
    rw [hg, Finset.sum_add_distrib, Finset.sum_add_distrib, hs, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring

theorem val_g_one (h : 1 < p ^ f - 1) : Q.intValuation (D.g 1) = Q.intValuation (D.ζ - 1) := by
  obtain ⟨y, hy, hg⟩ := D.exists_g_one_eq h
  have hn : -1 + y ∉ Q.asIdeal := by
    intro hm
    have h1 : (1 : A) ∈ Q.asIdeal := by
      have := Q.asIdeal.sub_mem hy hm
      simpa using this
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  rw [hg, map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr hn, mul_one]

end GSDatum

end DiscreteGroups.sglob.Stick
