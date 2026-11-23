import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af

namespace UpperTheory.V.Keep

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}

def SafeU (l : ℕ) [Fact l.Prime] (M : ℕ) (m : Fin n → ℤ) (_r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := l ∣ M ∨ ∀ i j, m i ≠ m j + 1

def SafeP (l : ℕ) [Fact l.Prime] (M : ℕ) (m : Fin n → ℤ) (_r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := l ∣ M ∨ ∀ i j, m i ≠ m j + 1

def OddU (l : ℕ) [Fact l.Prime] (_r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := Odd n

variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}

theorem safeUGap (_ : Level l M m r) (h : ∀ i j, m i ≠ m j + 1) : SafeU l M m r := Or.inr h

theorem oddTw (μ : G F Ω →* (Qbar l)ˣ) (h : OddU l r) : OddU l (tw r μ) := h

end UpperTheory.V.Keep
