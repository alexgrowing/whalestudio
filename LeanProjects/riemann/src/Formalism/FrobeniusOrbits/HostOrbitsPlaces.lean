import Formalism.FrobeniusOrbits.Statement

open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def HostOrbits : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) →
    (∀ τ ∈ Psi e, ∀ i : ℕ, φ ^ i * τ ∈ Psi e ↔ Even i) ∧
    (φ.1 = c0 → φ.2 ≠ 1 → Even (orderOf φ.2) ∧ orderOf φ = orderOf φ.2)

def placeOf {e : ℕ} (g : GG e) : GG e := if g.1.2 = 1 then g else cc e * g

def HostOrbitsPlaces : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) → ∀ τ ∈ Psi e, ∀ i : ℕ,
    (placeOf (φ ^ i * τ)).2 = φ.2 ^ i * τ.2 ∧
    (φ.1 = c0 → (placeOf (φ ^ i * τ)).1 = τ.1) ∧
    (φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
      (placeOf (φ ^ i * τ)).1 = (if Even i then 1 else (sg e).1) * τ.1)

def HostOrbitCount : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, φ.1 = c0 → ∀ τ ∈ Psi e,
    (Set.range fun i : ℕ => placeOf (φ ^ i * τ)).ncard = orderOf φ.2

def HostFiniteOrder : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (k g : ℕ), g.Prime → ∀ M : Matrix (Fin k) (Fin k) (hostE ζ a b), M ^ g = 1 → M ≠ 1 →
    g - 1 ≤ 2 ^ (e + 2) * k

end Formalism.FrobeniusOrbits
