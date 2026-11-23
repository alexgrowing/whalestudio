import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

abbrev OCp (p : Nat.Primes) : Type :=
  (NormedField.valuation (K := ℂ_[p])).valuationSubring

def inE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    E →+* c.F := τ.codRestrict c.F.toSubfield (c.conj τ)

def stdLat (A C : Type) [CommRing A] [Field C] [Algebra A C] (g : ℕ) : Submodule A (Fin g → C) where
  carrier := {x | ∀ i, x i ∈ (algebraMap A C).range}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun a x hx i => by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ (hx i)

section Eval

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs]
  {C : Type} [Field C] {g : ℕ}

def comb {R : Subring Ω} (ℓ : Fin g → Vs) (x : Fin g → R) : Vs := ∑ i, (x i : Ω) • ℓ i

def Tied {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρ : 𝓞 E →+* Module.End Ω Vs)
    (ρC : 𝓞 E →+* Module.End C (Fin g → C)) : Prop :=
  ∀ (a : 𝓞 E) (x x' : Fin g → R), ρ a (comb ℓ x) = comb ℓ x' → ρC a (fun i => ψ (x i)) = fun i => ψ (x' i)

def HodgeAt {R : Subring Ω} {N : ℕ} (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (HL : Submodule R (Vs × Module.Dual Ω Vs)) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs) : Prop :=
  HT.IsFreeOn ρH HL t ∧
    HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) = Submodule.span R (Set.range ℓ) ∧
    ∀ f : Module.Dual Ω Vs, ((0 : Vs), f) ∈ HL ↔ ∀ e ∈ Submodule.span R (Set.range ℓ), f e ∈ R

def IsEval {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R (Vs × Module.Dual Ω Vs))
    (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C)) : Prop :=
  (∀ (a : 𝓞 E) (h : HL) (h' : ρH a (h : Vs × Module.Dual Ω Vs) ∈ HL), ev ⟨_, h'⟩ = ρHC a (ev h)) ∧
  (∀ (h : HL) (x : Fin g → R), (h : Vs × Module.Dual Ω Vs).1 = comb ℓ x → (ev h).1 = fun i => ψ (x i)) ∧
  (∀ (h : HL) (x : Fin g → R) (r : R), (h : Vs × Module.Dual Ω Vs).1 = 0 →
    (h : Vs × Module.Dual Ω Vs).2 (comb ℓ x) = r → (ev h).2 (fun i => ψ (x i)) = ψ r)

end Eval
end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
