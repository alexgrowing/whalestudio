import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BLval

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_lprim :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), 1 ≤ k → χ.LFunction (1 - k) = -genB k χ / k ∧ Lprim χ (1 - k) = -Bprim k χ / k := by
  intro N _ χ k hk
  refine ⟨UpperTheory.V.Bern.b_lval χ k hk, ?_⟩
  unfold UpperTheory.V.Bern.Lprim UpperTheory.V.Bern.Bprim
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  exact UpperTheory.V.Bern.b_lval _ k hk
