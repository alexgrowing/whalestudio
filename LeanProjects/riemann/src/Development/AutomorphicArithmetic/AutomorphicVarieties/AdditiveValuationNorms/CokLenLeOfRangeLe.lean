import Mathlib

noncomputable section

namespace UpperTheory.V.PropA

variable (l : ℕ) [Fact l.Prime]

def GenBy (R : ℕ) (X : Type) [AddCommGroup X] [Module ℤ_[l] X] : Prop :=
  ∃ π : (Fin R → ℤ_[l]) →ₗ[ℤ_[l]] X, Function.Surjective π

abbrev jZero (l R : ℕ) : ℕ := Nat.log l R + 3

abbrev vl (x : ℤ_[l]) : ℕ∞ := IsDiscreteValuationRing.addVal ℤ_[l] x

def IsLevel (u : ℤ_[l]) (c : ℕ) : Prop := vl l (u - 1) = c ∧ 1 ≤ c ∧ (l = 2 → 2 ≤ c)

variable {l} {X : Type} [AddCommGroup X] [Module ℤ_[l] X]

def cokLen (f : Module.End ℤ_[l] X) : ℕ∞ := Module.length ℤ_[l] (X ⧸ LinearMap.range f)

def InPow (k : ℕ) (f : Module.End ℤ_[l] X) : Prop := ∀ x : X, ∃ y : X, f x = (l : ℤ_[l]) ^ k • y

def Unip (γ : Module.End ℤ_[l] X) : Prop := ∃ N : ℕ, InPow 1 ((γ - 1) ^ N)

def twLen (γ : Module.End ℤ_[l] X) (u : ℤ_[l]) (e m : ℕ) : ℕ∞ := cokLen ((u ^ e • γ) ^ l ^ m - 1)

theorem cokLen_le_of_range_le {f g : Module.End ℤ_[l] X} (h : LinearMap.range g ≤ LinearMap.range f) :
    cokLen f ≤ cokLen g :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

end UpperTheory.V.PropA

end
