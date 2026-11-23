import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInjectiveCharacter
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_injective_char (p : ℕ) [Fact p.Prime] :
    ∃ lam0 : (ZMod p)ˣ →* ℂˣ, Function.Injective lam0 :=
  _root_.UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char p

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.charOrd : CharOrd := by
  intro p _ ℓ k a hℓ hdvd
  obtain ⟨lam0, hinj⟩ := exists_injective_char p
  have hm0 : 0 < orderOf (a ^ 2) := orderOf_pos _
  have h2m : orderOf a ∣ 2 * orderOf (a ^ 2) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  have hlk : ℓ ^ k ∣ orderOf (a ^ 2) := by
    have h1 : ℓ ^ (k + 1) ∣ 2 * orderOf (a ^ 2) := hdvd.trans h2m
    by_cases h2 : ℓ = 2
    · subst h2
      rw [pow_succ, mul_comm] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    · have hc : Nat.Coprime (ℓ ^ (k + 1)) 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hℓ Nat.prime_two).mpr h2)
      exact (Dvd.intro _ (pow_succ ℓ k).symm).trans (hc.dvd_of_dvd_mul_left h1)
  obtain ⟨e, he⟩ := hlk
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      omega
    · exact h
  have hlpos : 0 < ℓ ^ k := pow_pos hℓ.pos k
  refine ⟨lam0 ^ (2 * e), ?_, ?_⟩
  · rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    simp
  · have h1 : (lam0 ^ (2 * e)) a = (lam0 (a ^ 2)) ^ e := by
      rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    have h2 : orderOf (lam0 (a ^ 2)) = ℓ ^ k * e := by
      rw [orderOf_injective lam0 hinj, he]
    rw [h1, orderOf_pow' _ hepos.ne', h2, Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ hepos]
