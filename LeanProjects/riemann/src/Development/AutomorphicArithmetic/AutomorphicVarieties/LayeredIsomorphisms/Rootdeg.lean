import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.rootdeg :
    ∀ (L : Type) [Field L] [NumberField L] (l k : ℕ), l.Prime → (∃ ζ : L, IsPrimitiveRoot ζ (l ^ k)) →
      l ^ k ≤ 2 * Module.finrank ℚ L := by
  intro L _ _ l k hl ⟨ζ, hζ⟩
  have hpos : 0 < l ^ k := pow_pos hl.pos k
  have ht : (l ^ k).totient ≤ Module.finrank ℚ L := by
    have h1 := hζ.lcm_totient_le_finrank (K := ℚ) hζ
      (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
    rwa [Nat.lcm_self] at h1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, Nat.totient_one] at ht ⊢
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow hl hk, Nat.add_sub_cancel] at ht
    have h2 : l ≤ 2 * (l - 1) := by
      have := hl.two_le
      omega
    calc l ^ (m + 1) = l ^ m * l := pow_succ l m
      _ ≤ l ^ m * (2 * (l - 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 * (l ^ m * (l - 1)) := by ring
      _ ≤ 2 * Module.finrank ℚ L := Nat.mul_le_mul_left _ ht
