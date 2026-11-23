import Mathlib

noncomputable section

namespace PI.LatLocGlob

def loc {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (p : Ideal R) (L : Submodule R V) : Set V :=
  {x | ∃ s : R, s ∉ p ∧ s • x ∈ L}

def IsFullLat (K : Type) {R V : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] (L : Submodule R V) : Prop :=
  L.FG ∧ Submodule.span K (L : Set V) = ⊤

def LatLocGlob : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (L0 : Submodule R V), IsFullLat K L0 →
    ∀ M : Ideal R → Set V,
      (∀ p : Ideal R, p.IsMaximal → ∃ N : Submodule R V, IsFullLat K N ∧ M p = loc p N) →
      Set.Finite {p : Ideal R | p.IsMaximal ∧ M p ≠ loc p L0} →
      ∃! L : Submodule R V, IsFullLat K L ∧ ∀ p : Ideal R, p.IsMaximal → loc p L = M p

end PI.LatLocGlob
