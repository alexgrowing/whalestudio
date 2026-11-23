import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

private theorem key_primeq {R : Type} [CommRing R] [Algebra ℚ R] {M c c' : ℕ} [NeZero M] (k : ℕ)
    (ψ : DirichletCharacter R c) (ψ' : DirichletCharacter R c') (e : c = c') (h : c ∣ M) (h' : c' ∣ M)
    (hψ : DirichletCharacter.changeLevel h ψ = DirichletCharacter.changeLevel h' ψ') :
    genB k (ψ : ZMod c → R) = genB k (ψ' : ZMod c' → R) ∧ ∀ a : ℕ, ψ (a : ZMod c) = ψ' (a : ZMod c') := by
  subst e
  have hψψ : ψ = ψ' := DirichletCharacter.changeLevel_injective h hψ
  subst hψψ
  exact ⟨rfl, fun _ => rfl⟩

theorem UpperTheory.V.Bern.b_primeq :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (χ.IsPrimitive → Bprim k χ = genB k χ ∧ ∀ a : ℕ, primVal χ a = χ (a : ZMod N)) ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), Bprim k (DirichletCharacter.changeLevel h χ) = Bprim k χ ∧ ∀ a : ℕ, primVal (DirichletCharacter.changeLevel h χ) a = primVal χ a := by
  intro R _ _ N _ k χ
  refine ⟨fun hp => ?_, fun M _ h => ?_⟩
  · exact key_primeq k χ.primitiveCharacter χ hp χ.conductor_dvd_level (dvd_refl N)
      (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_self])
  · refine key_primeq k (DirichletCharacter.changeLevel h χ).primitiveCharacter χ.primitiveCharacter
      (DirichletCharacter.conductor_changeLevel χ h) (DirichletCharacter.conductor_dvd_level _)
      (χ.conductor_dvd_level.trans h) ?_
    rw [DirichletCharacter.changeLevel_primitiveCharacter,
      DirichletCharacter.changeLevel_trans _ χ.conductor_dvd_level h,
      DirichletCharacter.changeLevel_primitiveCharacter]
