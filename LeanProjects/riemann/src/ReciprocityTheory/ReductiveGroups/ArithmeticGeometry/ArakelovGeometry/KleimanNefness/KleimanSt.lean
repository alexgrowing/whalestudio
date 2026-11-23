import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def NefOnV {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (α : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → V ≤ W →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 ≤ geoNum 1 W (fun _ => α)

def NefOnF {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
    (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (α : K → ℤ) : Prop :=
  ∀ W : Ideal (MRingOver F ι), IsProjVarF W 1 → V ≤ W → 0 ≤ I W 1 ![α]

def KleimanNefIntersectionNonneg : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (n : ℕ)
    (a : Fin n → K → ℤ),
    IsMultiProjPrime V → charOf V ≠ 0 →
    ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ j, NefOnV V (a j)) → 0 ≤ geoNum n V a

def KleimanNefFStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) (a : Fin n → K → ℤ),
    IsFieldIntersection I → IsProjVarF V n → (∀ j, NefOnF I V (a j)) → 0 ≤ I V n a

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
