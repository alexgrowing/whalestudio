import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

variable {k : Type} [CommRing k] {d n : ℕ}

def dAdd (u : Fin d → k) (b : Fin n) (G : PS k n d) : PS k n d :=
  ∑ j : Fin d, C (u j) * pderiv k (b, j) G

def polyAdd {ι : Type} [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k) (G : PS k n d) :
    PS k n d :=
  ∑ m ∈ P.support, C (P.coeff m) *
    (Finset.univ : Finset (ι × Fin n)).toList.foldr (fun p g => (dAdd (u p.1) p.2)^[m p] g) G

def quadCol (β : Matrix (Fin d) (Fin d) k) : PS k n d :=
  ∑ b : Fin n, ∑ i : Fin d, ∑ j : Fin d, C (β i j) * X (b, i) * X (b, j)

def KillAddSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → k)
    (β : Matrix (Fin d) (Fin d) k) (P : MvPolynomial (ι × Fin n) k),
    secondOrder k (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0) P = 0 →
    ∀ (m : k) (g : PS k n d),
      constantCoeff (polyAdd u P (FB.expS k (m • quadCol (n := n) β) * g)) = constantCoeff (polyAdd u P g)

end ReciprocityTheory.ChartRestriction.G.TB
