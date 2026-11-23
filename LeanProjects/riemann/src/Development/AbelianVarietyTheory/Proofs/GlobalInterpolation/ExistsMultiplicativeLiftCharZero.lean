import Mathlib

namespace GlobalTheory

theorem charZero_wittVector_of_field (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h3 : p ∣ l := (CharP.cast_eq_zero_iff K p l).1 h2
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h3
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

theorem exists_multiplicative_lift_charZero :
    ∀ (K : Type) [Field K], ∃ (K' : Type) (_ : Field K') (_ : CharZero K') (τ : K →*₀ K'), Function.Injective τ ∧ ∀ (ι : Type) (s : Finset ι) (f : ι → K), ∑ i ∈ s, τ (f i) = 0 → ∑ i ∈ s, f i = 0 := by
  intro K _
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with h | h
  · haveI : Fact p.Prime := ⟨h⟩
    haveI := charZero_wittVector_of_field p K
    have hinj := IsFractionRing.injective (WittVector p K) (FractionRing (WittVector p K))
    haveI : CharZero (FractionRing (WittVector p K)) := charZero_of_injective_algebraMap hinj
    let τ : K →*₀ FractionRing (WittVector p K) :=
      { toFun := fun a => algebraMap (WittVector p K) _ (WittVector.teichmuller p a)
        map_zero' := by simp
        map_one' := by simp
        map_mul' := by intro a b; simp }
    have hτ : ∀ a, τ a = algebraMap (WittVector p K) _ (WittVector.teichmuller p a) := fun _ => rfl
    have hc : ∀ a : K, (WittVector.constantCoeff : WittVector p K →+* K)
        (WittVector.teichmuller p a) = a := fun a => by
      simp [WittVector.constantCoeff_apply]
    refine ⟨FractionRing (WittVector p K), inferInstance, inferInstance, τ, ?_, ?_⟩
    · intro a b hab
      rw [hτ, hτ] at hab
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (hinj hab)
      rwa [hc, hc] at this
    · intro ι s f hf
      simp only [hτ] at hf
      rw [← map_sum, ← map_zero (algebraMap (WittVector p K) (FractionRing (WittVector p K)))] at hf
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (hinj hf)
      rw [map_sum, map_zero] at this
      simpa only [hc] using this
  · subst h
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ⟨K, inferInstance, inferInstance, MonoidWithZeroHom.id K, fun _ _ h => h, fun _ _ _ h => h⟩

end GlobalTheory
