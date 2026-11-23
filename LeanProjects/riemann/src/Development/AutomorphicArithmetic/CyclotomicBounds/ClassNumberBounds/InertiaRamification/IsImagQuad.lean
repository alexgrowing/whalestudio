import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.LogRootDiscChar

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

noncomputable def resDeg [NeZero N] (l : ℕ) [Fact l.Prime]
    (X : Subgroup (DirichletCharacter ℂ N)) : ℕ :=
  (inertiaUnits N l ⊔ charKer X).relIndex (decompUnits N l ⊔ charKer X)

noncomputable def numPlaces [NeZero N] (l : ℕ) [Fact l.Prime]
    (X : Subgroup (DirichletCharacter ℂ N)) : ℕ :=
  (decompUnits N l ⊔ charKer X).index

noncomputable def condDvd (N m : ℕ) : Subgroup (DirichletCharacter ℂ N) :=
  annihilator ℂ ((ZMod.unitsMap (Nat.gcd_dvd_left N m)).ker : Set (ZMod N)ˣ)

def IsImagQuad (ψ : DirichletCharacter ℂ N) (d : ℕ) : Prop :=
  ψ ^ 2 = 1 ∧ ψ.Odd ∧ ψ.conductor = d

noncomputable def hostChars (n : ℕ) (ch ps χ : DirichletCharacter ℂ N) :
    Subgroup (DirichletCharacter ℂ N) :=
  Subgroup.closure {ch, ps} ⊔ (evenPart (condDvd N (4 * n)) ⊔ Subgroup.zpowers χ)

def HostData (n d q₁ : ℕ) (ch ps χ : DirichletCharacter ℂ N) : Prop :=
  (∃ e, 2 ≤ e ∧ n = 2 ^ e) ∧ 4 * n ∣ N ∧ d.Prime ∧ d % 16 = 7 ∧ q₁.Prime ∧ q₁ % 8 = 3 ∧
    IsImagQuad ch d ∧ IsImagQuad ps q₁ ∧ ¬ d ∣ χ.conductor ∧ ¬ q₁ ∣ χ.conductor

end KStar.Ram
