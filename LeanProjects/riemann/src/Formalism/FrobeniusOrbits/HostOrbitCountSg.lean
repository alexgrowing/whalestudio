import Formalism.FrobeniusOrbits.HostOrbitsPlaces

noncomputable section

namespace Formalism.FrobeniusOrbits

def HostOrbitCountSg : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) → ∀ τ ∈ Psi e,
    orderOf φ = Nat.lcm 2 (orderOf φ.2) ∧
    (Set.range fun i : ℕ => placeOf (φ ^ i * τ)).ncard = orderOf φ

end Formalism.FrobeniusOrbits
