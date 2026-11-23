import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def jetLB {k : Type} [Field k] (P : PolAV (Spec (CommRingCat.of k)))
    (a₀ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (q : ℕ) :
    LB (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left :=
  LB.LinComb P.L (K := Fin 3)
    ![(snd (baseOver (Spec (CommRingCat.of k))) P.A).left, (translPt P.A a₀).left,
      (snd (baseOver (Spec (CommRingCat.of k))) P.A).left] ![(q : ℤ), 1, -1]

def JetLemmaStatement : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (P : PolAV (Spec (CommRingCat.of k)))
    (a₀ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (q D : ℕ), 4 * D + 4 ≤ q →
    ∀ y ∈ Set.range (ptSecT P.A x).left.base,
    ∀ (j : (jetLB P a₀ q).ι) (hy : y ∈ (jetLB P a₀ q).U j)
      (f : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left.presheaf.stalk y),
      ∃ s : LB.Sec (jetLB P a₀ q),
        ((baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left.presheaf.germ
            ((jetLB P a₀ q).U j) y hy).hom (s.f j) - f ∈
          IsLocalRing.maximalIdeal
            ((baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left.presheaf.stalk y) ^ (D + 1)

end ReciprocityTheory.ChartRestriction.G.H1
