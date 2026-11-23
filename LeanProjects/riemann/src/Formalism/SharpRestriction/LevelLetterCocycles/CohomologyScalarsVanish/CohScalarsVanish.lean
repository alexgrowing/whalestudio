import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem

noncomputable section

namespace Formalism.MainNotions.N.CohomologyScalarsVanish

open ReciprocityTheory.Gal

def CohScalarsVanish : Prop :=
  ∀ (n : ℕ) (k : Type) [CommRing k] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module k M] [Module (ZMod n) M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul k M] [ContinuousConstSMul (ZMod n) M]
    (rho : Representation k G M) (rho' : Representation (ZMod n) G M), (∀ g m, rho' g m = rho g m) →
    (H0 rho' = ⊥ ∧ Subsingleton (H1 rho') ∧ Subsingleton (H2 rho')) →
      H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho)

end Formalism.MainNotions.N.CohomologyScalarsVanish
