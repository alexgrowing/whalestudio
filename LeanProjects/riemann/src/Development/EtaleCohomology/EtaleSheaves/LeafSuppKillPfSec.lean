import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafTwSecKill : Prop := ∀ (q : ℕ) [NeZero q] {X Z : Scheme.{0}} [IsNoetherian X] (ι : Z ⟶ X) [IsClosedImmersion ι],
  IsUnit (q : Γ(X, ⊤)) → ∀ (j : ℤ) (s : Sec (tw q j) X), Sec.res ι s = 0 →
  ∀ x ∈ Set.range ι, ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ x ∈ Set.range w ∧ Sec.res w s = 0

end LateralTheory.E.E8
