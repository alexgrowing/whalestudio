import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdeal
import Development.WeilBound.CoreStatements.SesquilinearFractions.RatProductFormula
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

namespace NP

open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

theorem norm_int_le {p : Nat.Primes} (j : k →+* ℂ_[p]) (a : 𝓞 k) : ‖j (a : k)‖ ≤ 1 :=
  NI.norm_int_le (j.comp (algebraMap (𝓞 k) k)) a

theorem norm_p_lt (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [NR.norm_padicNat, padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)

def vj {p : Nat.Primes} (j : k →+* ℂ_[p]) : HeightOneSpectrum (𝓞 k) where
  asIdeal :=
    { carrier := {a | ‖(j.comp (algebraMap (𝓞 k) k)) a‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        rw [map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le j c)).trans_lt ha }
  isPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (Ideal.eq_top_iff_one _).1 h
      simp at this
    · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hab ⊢
      rw [map_mul, norm_mul] at hab
      by_contra h
      push_neg at h
      have ha := le_antisymm (NI.norm_int_le (j.comp (algebraMap (𝓞 k) k)) a) h.1
      have hb := le_antisymm (NI.norm_int_le (j.comp (algebraMap (𝓞 k) k)) b) h.2
      rw [ha, hb, one_mul] at hab
      exact lt_irrefl _ hab
  ne_bot := by
    intro h
    have : ((p : ℕ) : 𝓞 k) ∈ (⊥ : Ideal (𝓞 k)) := by
      rw [← h]
      show ‖(j.comp (algebraMap (𝓞 k) k)) ((p : ℕ) : 𝓞 k)‖ < 1
      rw [map_natCast]
      exact norm_p_lt p
    rw [Ideal.mem_bot] at this
    exact p.2.ne_zero (by exact_mod_cast this)

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 k)) : ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
  have hP : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 k) ∈ v.asIdeal → ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd (by simpa using h) (v.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2)
    | prime q hq => intro _ h; exact ⟨⟨q, hq⟩, h⟩
    | mul a b ha hb =>
      intro hab h
      rw [Nat.cast_mul] at h
      rcases v.isPrime.mem_or_mem h with h | h
      · exact ha (fun h0 => hab (by rw [h0, zero_mul])) h
      · exact hb (fun h0 => hab (by rw [h0, mul_zero])) h
  exact hP _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem v.asIdeal)

theorem prime_unique (v : HeightOneSpectrum (𝓞 k)) {p q : Nat.Primes} (hp : ((p : ℕ) : 𝓞 k) ∈ v.asIdeal)
    (hq : ((q : ℕ) : 𝓞 k) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes p.2 q.2).2 fun h => hne (Subtype.ext h)
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 k))
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huw]
  simp only [eq_intCast, Int.cast_natCast]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hq)

theorem finite_over (p : Nat.Primes) : {v : HeightOneSpectrum (𝓞 k) | ((p : ℕ) : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((p : ℕ) : 𝓞 k)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end NP

end PositivityTheory.Xgf
