import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG

open MvPolynomial

variable {D : ℕ}

noncomputable def liftHom (a : Fin D → ℂ) :
    MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (Fin D) ℂ) :=
  aeval fun i => Polynomial.C (C (a i)) + Polynomial.C (X i - C (a i)) * Polynomial.X

end ReciprocityTheory.ChartRestriction.G.AR.Up.PG

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

end ReciprocityTheory.ChartRestriction.G.AR.Up
