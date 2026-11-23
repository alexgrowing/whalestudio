import Mathlib
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups
namespace Formalism.ConjugateSelfDual
abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

abbrev Qbar (l : ℕ) [Fact l.Prime] := PadicAlgCl l

def cyc (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    G F Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter (Ω) l).comp
      (MulSemiringAction.toRingAut (G F Ω) (Ω)))

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def IsPlaceOver (A : ValuationSubring (Ω)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F (Ω) (x : F)) < 1 ↔ x ∈ v.asIdeal

def normV (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

def Inertia (A : ValuationSubring (Ω)) : Set (G F Ω) :=
  {σ | σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}

def IsFrob (A : ValuationSubring (Ω)) (q : ℕ) (σ : G F Ω) : Prop :=
  σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1

end places
end Formalism.ConjugateSelfDual
end
