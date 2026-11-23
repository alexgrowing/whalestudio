import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAway

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

def intAfP (p : ℕ) : Set (AfP p) :=
  {a | ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem natCast_mem (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  _root_.natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.2 hb0, ?_⟩
  have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (|b|) := by
    rw [← Int.natCast_natAbs, map_natCast]
  rw [e]
  rcases abs_choice b with h | h
  · rw [h, mul_comm]; exact hbx
  · rw [h, map_neg, neg_mul, mul_comm]; exact neg_mem hbx

theorem eval_natCast_mul {p : ℕ} (v : AwayP p) (n : ℕ) (a : AfP p) :
    AfP.eval v ((n : AfP p) * a) = (n : v.1.adicCompletion ℚ) * AfP.eval v a := by
  rw [map_mul, map_natCast]

theorem exists_nat_adele {p : ℕ} (a : AfP p) : ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 (AfP.eval v a)
  have hS : {v : AwayP p | ¬ AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (a : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [eval_natCast_mul]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem w.1 k) (hm w)
  · have hw' : AfP.eval w a ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem w.1 _) hw'

theorem exists_pow_of_integral_away (p : ℕ) [Fact p.Prime] (r : ℚ)
    (h : ∀ v : AwayP p, (v.1.valuation ℚ r) ≤ 1) : ∃ (k : ℤ) (e : ℕ), r * (p : ℚ) ^ e = k := by
  have hden : r.den = p ^ r.den.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd r.den_nz fun {ℓ} hℓ hdvd => ?_
    by_contra hne
    have hℓ' : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
    let v : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)}, (Ideal.span_singleton_prime hℓ'.ne_zero).2 hℓ',
      by simpa using hℓ.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro h'
      have h'' : Associated (ℓ : ℤ) (p : ℤ) := Ideal.span_singleton_eq_span_singleton.1 h'
      exact hne (by simpa using Int.natAbs_eq_iff_associated.2 h'')
    have h1 := Rat.valuation_le_one_iff_den.1 (h ⟨v, hv⟩)
    exact h1 (Ideal.mem_span_singleton.2 (by exact_mod_cast hdvd))
  refine ⟨r.num, r.den.primeFactorsList.length, ?_⟩
  have : ((p : ℚ) ^ r.den.primeFactorsList.length) = (r.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.mul_den_eq_num]

theorem den_bounded_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Ω : Set (AfP p)), IsCompact Ω → ∃ M : ℕ, 0 < M ∧
    ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Ω → ∃ (k : ℤ) (e : ℕ), q * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  intro p _ Ω hΩ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun q hq => ?_⟩
  obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (ht hq)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hqa' : (m a : AfP p) * algebraMap ℚ (AfP p) q ∈ intAfP p := hqa
  have hint : ∀ v : AwayP p, v.1.valuation ℚ (((∏ a ∈ t, m a : ℕ) : ℚ) * q) ≤ 1 := by
    intro v
    have h2 : AfP.eval v (algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q)) ∈
        v.1.adicCompletionIntegers ℚ := by
      have e : algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q) =
          (k : AfP p) * ((m a : AfP p) * algebraMap ℚ (AfP p) q) := by
        rw [map_mul, map_natCast, hk, Nat.cast_mul]; ring
      rw [e, eval_natCast_mul]
      exact mul_mem (natCast_mem v.1 k) (hqa' v)
    rw [AlgHom.commutes] at h2
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    exact h2
  obtain ⟨z, e, hz⟩ := exists_pow_of_integral_away p _ hint
  exact ⟨z, e, by rw [← hz]; ring⟩

end GlobalTheory.DenAway
