import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.KBridgeOfKPublished

noncomputable section

open CategoryTheory NumberField IsDedekindDomain UpperTheory.V.KL UpperTheory.V.Published
open scoped TensorProduct

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

namespace UpperTheory.V.Published

def KHurewiczW : Prop :=
  ∀ (R : Type) [CommRing R] (M : Plus R) (k : ℕ) (h : Additive (M.K (k + 2)) →+ singH M.X (k + 2)),
    IsHurewicz M.X M.pt (k + 2) (fun a => h (Additive.ofMul a)) → ∀ l : ℕ, l.Prime →
      ∃ u : ℕ, Nat.Coprime u l ∧ ∀ x, h x = 0 → (l ^ K.cOne (k + 2) * u) • x = 0

end UpperTheory.V.Published

namespace UpperTheory.V.K

end UpperTheory.V.K

namespace UpperTheory.V

structure Published.KPublishedW : Prop where
  plusExists : KPlusExists
  acyclicHomology : KAcyclicHomology
  milnor : KMilnor
  hurewicz : KHurewiczW
  stability : KStability
  finGen : KFinGen
  borelRank : KBorelRank
  dwyerFriedlander : KDwyerFriedlander

end UpperTheory.V

end
