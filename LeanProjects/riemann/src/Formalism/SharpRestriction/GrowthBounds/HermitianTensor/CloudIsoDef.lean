import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

def CloudIsoP : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    (w : O), Irreducible w → ∀ (n' m : ℕ) (mu ze : Fin n' → Fin (m + 1) → ℤ), (∀ s, Antitone (mu s)) →
    (∀ s, Antitone (ze s)) → ∀ M : Fin n' → Submodule O (Fin (m + 1) → K), (∀ s, IsLattice O (M s)) →
    ∀ z : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, (∀ s, z s ∈ H0 O m (ze s) (M s)) →
    (∀ s, ¬ ∃ z' ∈ H0 O m (ze s) (M s), z s = w • z') →
    ∀ F ∈ tensorLat K K (fun s => dualWeyl K (m + 1) (m + 1) (nuOf (mu s))),
      (∏ s, blockEmb K s (z s)) * F ∈ tensorLat O K (fun s => H0 O m (mu s + ze s) (M s)) →
      F ∈ tensorLat O K (fun s => H0 O m (mu s) (M s))

end Formalism.MainNotions.flipOneThree.Pf

end
