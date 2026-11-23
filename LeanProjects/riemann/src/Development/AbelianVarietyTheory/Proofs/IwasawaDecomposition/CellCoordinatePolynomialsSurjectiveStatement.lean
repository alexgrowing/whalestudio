import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatePolynomialsSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinate_polynomials_surjective : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (w : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → ∑ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D w q) * gxi a b hk c w q = 1 ∧ Function.Surjective (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)) := by
  first | exact @GlobalTheory.GrCl.CellGen.main | exact GlobalTheory.GrCl.CellGen.main | (intros; apply GlobalTheory.GrCl.CellGen.main <;> assumption)
