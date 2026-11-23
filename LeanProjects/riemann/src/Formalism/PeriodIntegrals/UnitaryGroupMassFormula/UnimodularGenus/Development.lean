import Mathlib
import Formalism.PeriodIntegrals.UnimodGenus

open NumberField

noncomputable section

namespace PI.UG.W

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def locR (p : Ideal R) : Submodule R K := loc (K := K) p (1 : Submodule R K)

def dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (locR (K := K) p).comap ((h y).restrictScalars R)

def IsUnimodularAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) : Prop :=
  dualAt h p (loc (K := K) p L) = loc (K := K) p L

end Defs

def UnimodLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ),
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
      ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt (hStd E n) p N

def IsomLocStd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), IsCMUnram E →
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N →
      ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt (hStd E n) p N →
        ∃ g ∈ isom (hStd E n), gmap g (loc (K := E) p (stdLat E n)) = loc (K := E) p N

theorem unimodGenus_of (h1 : UnimodLocal) (h2 : IsomLocStd) : PI.UnimodGenus := by
  intro E _ _ _ n hE N hN hU p hp
  exact h2 E n hE N hN p hp (h1 E n N hN hU p hp)

end PI.UG.W
