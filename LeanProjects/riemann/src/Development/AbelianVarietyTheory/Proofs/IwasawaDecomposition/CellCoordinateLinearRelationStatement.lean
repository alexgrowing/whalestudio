import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinateLinearRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinate_linear_relation : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R), a ≤ k → k ≤ b → LeftInv D c → ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → GPm m a b) (e : T → R), ∀ w' : GPm m a b, gxi a b hk c w' q = ∑ t, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (e t) * ∑ q', (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D (jj t) q') * gxi a b hk c w' q' := by
  first | exact @GlobalTheory.GrCl.CellLin.main | exact GlobalTheory.GrCl.CellLin.main | (intros; apply GlobalTheory.GrCl.CellLin.main <;> assumption)
