import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.FactorizationMultisetProd

namespace PI.Residue

open NumberField Ideal UniqueFactorizationMonoid
open scoped ENNReal

variable (E : Type*) [Field E] [NumberField E]

def primeSet : Set (Ideal (𝓞 E)) := {P | P.IsPrime ∧ P ≠ ⊥}

variable {E}

theorem one_lt_absNorm_of_mem {P : Ideal (𝓞 E)} (hP : P ∈ primeSet E) : 1 < absNorm P := by
  have h0 : absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hP.2
  have h1 : absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.1.ne_top
  omega

variable (E)

set_option linter.deprecated false in
theorem exists_injOn_primesOver (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) :
    ∃ g : Ideal (𝓞 E) → Fin (Module.finrank ℚ E), Set.InjOn g (p.primesOver (𝓞 E)) := by
  have hcard := Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hp
  have : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hfin : (p.primesOver (𝓞 E)).Finite := by
    rw [← IsDedekindDomain.coe_primesOverFinset hp (𝓞 E)]
    exact Finset.finite_toSet _
  obtain ⟨f, -, hf⟩ := hfin.exists_injOn_of_encard_le
    (t := (Set.univ : Set (Fin (Module.finrank ℚ E)))) (by
      rw [← IsDedekindDomain.coe_primesOverFinset hp (𝓞 E), Set.encard_coe_eq_coe_finsetCard,
        Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      exact_mod_cast hcard)
  exact ⟨f, hf⟩

variable {E}

theorem under_eq_of_not_coprime {P Q : Ideal (𝓞 E)} (hP : P ∈ primeSet E) (hQ : Q ∈ primeSet E)
    (hcop : ¬ Nat.Coprime (absNorm P) (absNorm Q)) : P.under ℤ = Q.under ℤ := by
  have := hP.1
  have := hQ.1
  have : NeZero P := ⟨hP.2⟩
  have : NeZero Q := ⟨hQ.2⟩
  have pP := Nat.absNorm_under_prime P
  have pQ := Nat.absNorm_under_prime Q
  have eP := absNorm_eq_pow_inertiaDeg'_of_liesOver P (P.under ℤ) inferInstance
    (Ideal.under_ne_bot ℤ hP.2)
  have eQ := absNorm_eq_pow_inertiaDeg'_of_liesOver Q (Q.under ℤ) inferInstance
    (Ideal.under_ne_bot ℤ hQ.2)
  by_contra hne
  apply hcop
  rw [eP, eQ]
  apply Nat.Coprime.pow
  rw [Nat.coprime_primes pP pQ]
  intro heq
  apply hne
  rw [← Int.ideal_span_absNorm_eq_self (P.under ℤ), ← Int.ideal_span_absNorm_eq_self (Q.under ℤ),
    heq]

variable (E)

theorem exists_idx : ∃ idx : Ideal (𝓞 E) → Fin (Module.finrank ℚ E),
    ∀ P ∈ primeSet E, ∀ Q ∈ primeSet E, idx P = idx Q →
      ¬ Nat.Coprime (absNorm P) (absNorm Q) → P = Q := by
  classical
  have H : ∀ p : Ideal ℤ, ∃ g : Ideal (𝓞 E) → Fin (Module.finrank ℚ E),
      p.IsMaximal → p ≠ ⊥ → Set.InjOn g (p.primesOver (𝓞 E)) := by
    intro p
    by_cases h : p.IsMaximal ∧ p ≠ ⊥
    · have := h.1
      obtain ⟨g, hg⟩ := exists_injOn_primesOver E p h.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨fun _ => ⟨0, Module.finrank_pos⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using H
  refine ⟨fun P => g (P.under ℤ) P, ?_⟩
  intro P hP Q hQ hidx hcop
  have key := under_eq_of_not_coprime hP hQ hcop
  have := hP.1
  have := hQ.1
  have hbot : Q.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ hQ.2
  have hprime : (Q.under ℤ).IsPrime := inferInstance
  have hmax : (Q.under ℤ).IsMaximal := hprime.isMaximal hbot
  simp only [key] at hidx
  refine hg (Q.under ℤ) hmax hbot ⟨hP.1, ⟨key.symm⟩⟩ ⟨hQ.1, ⟨rfl⟩⟩ hidx

theorem exists_tuple : ∃ n : {I : Ideal (𝓞 E) // I ≠ ⊥} → Fin (Module.finrank ℚ E) → ℕ,
    Function.Injective n ∧ ∀ I, ∏ i, n I i = absNorm I.1 := by
  classical
  obtain ⟨idx, hidx⟩ := exists_idx E
  have hmem : ∀ (I : Ideal (𝓞 E)), ∀ P ∈ normalizedFactors I, P ∈ primeSet E := by
    intro I P hP
    have hp := prime_of_normalized_factor P hP
    exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩
  refine ⟨fun I => intersection_update_fsHerm_neg_one (fun P => absNorm P) idx (normalizedFactors I.1), ?_, ?_⟩
  · intro I J hIJ
    have := position_inj (fun P : Ideal (𝓞 E) => absNorm P) idx (primeSet E)
      (fun P hP => one_lt_absNorm_of_mem hP) hidx (hmem I.1) (hmem J.1) hIJ
    apply Subtype.ext
    rw [← Ideal.prod_normalizedFactors_eq_self I.2, ← Ideal.prod_normalizedFactors_eq_self J.2,
      this]
  · intro I
    rw [prod_position, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self I.2]

theorem tsum_ideal_le (w : ℕ →* ℝ≥0∞) :
    ∑' I : {I : Ideal (𝓞 E) // I ≠ ⊥}, w (absNorm I.1) ≤ (∑' k, w k) ^ Module.finrank ℚ E := by
  obtain ⟨n, hinj, hn⟩ := exists_tuple E
  refine tsum_le_pow n hinj w _ (fun I => ?_)
  rw [← hn I, map_prod]

end PI.Residue
