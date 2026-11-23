import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def FixIc (c : Coef l) (a : Qbar l) : Prop :=
  ∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ x : Qbar l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ a = a

def HTCoI (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω), (∀ i, ‖o i‖ ≤ 1 ∧ FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg (m - c₀) (Z m s y) (h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))

end GlobalTheory.LambdaValuationPowers
