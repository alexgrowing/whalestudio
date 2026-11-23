import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.GeneralizedBernoulliChangeLevel

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primlevel :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N), 0 < N → 1 ≤ k → genB k χ = Bprim k χ * ∏ p ∈ N.primeFactors, (1 - primVal χ p * (p : R) ^ (k - 1)) := by
  intro R _ _ N k χ hN hk
  have h := b_level χ.conductor_dvd_level k χ.primitiveCharacter hN hk
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  rw [h]
  rfl
