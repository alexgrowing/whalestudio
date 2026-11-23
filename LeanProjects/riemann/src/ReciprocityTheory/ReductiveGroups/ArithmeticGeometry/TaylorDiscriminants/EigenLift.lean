import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def BetaSesqSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (a : O) (ξ η : (Fin d → k) × (Fin d → k)),
    betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η)

def EigenOrthSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (χ χ' : O → k) (ξ η : (Fin d → k) × (Fin d → k)),
    (∀ a, OactH k B a ξ = χ a • ξ) → (∀ a, OactH k B a η = χ' a • η) →
    (∃ a, IsUnit (χ a - χ' (star a))) → betaH k ξ η = 0

end ReciprocityTheory.ChartRestriction.G.TB
