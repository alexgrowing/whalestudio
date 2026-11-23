import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.LimitEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Weil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure IneRel (x y : WD h) : Prop where
  pol : ∀ s, x.charPol (ineIncl h s) = y.charPol (ineIncl h s)
  eig : ∀ ξ, EigZero y ξ → EigZero x ξ

theorem IneRel.refl (x : WD h) : IneRel x x := ⟨fun _ => rfl, fun _ k => k⟩

end Weil

def KillTransfer : Prop :=
  ∀ (I V V' : Type) [Group I] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (ρ : Representation ℂ I V) (ρ' : Representation ℂ I V'), (Set.range ρ).Finite →
    (∀ s, LinearMap.trace ℂ V (ρ s) = LinearMap.trace ℂ V' (ρ' s)) →
    ∀ x : MonoidAlgebra ℂ I, ρ'.asAlgebraHom x = 0 → ρ.asAlgebraHom x = 0

def SplitOff : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (z : WDRep h V) (c : G E Ω → ℂ) (γ : ↥(Ine (F := E) A)) (q : ℂ[X]), q.eval (c γ) ≠ 0 →
    (∀ (g : Weil h) (s : ↥(Ine (F := E) A)), c (ineConj g s) = c s) →
    (∀ s : ↥(Ine (F := E) A), (z.ρ (ineIncl h s) - c s • 1) * aeval (z.ρ (ineIncl h γ)) q = 0) →
    (∀ s : ↥(Ine (F := E) A), aeval (z.ρ (ineIncl h γ)) q * (z.ρ (ineIncl h s) - c s • 1) = 0) →
    (∀ v, (∀ s : ↥(Ine (F := E) A), z.ρ (ineIncl h s) v = c s • v) → z.N v = 0) →
    UpperTheory.GalN.SplW c ((z.ρ (ineIncl h γ)).charpoly.rootMultiplicity (c γ)) (WD.mk z)

def SplOfRel : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), IneRel x y →
    ∀ (u : WD h) (c : G E Ω → ℂ) (t : ℕ), ∀ γ ∈ Ine (F := E) A, ((y.lpSum u).inePol γ).rootMultiplicity (c γ) ≤ t →
      UpperTheory.GalN.SplW c t (y.lpSum u) → UpperTheory.GalN.SplW c t (x.lpSum u)

def CommWild : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (s s' : G E Ω), s ∈ Ine (F := E) A →
    s' ∈ Ine (F := E) A → ∀ z : Ω, z ≠ 0 → A.valuation ((s * s' * s⁻¹ * s'⁻¹) z / z - 1) < 1

def AwOfRel : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.lpDim = y.lpDim → (y.unr → x = y) →
    (UpperTheory.GalS.TmW y → IneRel x y) → UpperTheory.GalS.Aw x y

end UpperTheory.Gal.NearKilling
