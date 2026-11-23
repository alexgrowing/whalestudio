import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChart
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzeroCoordinate_affineChart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  first | exact @GlobalTheory.ZM.CoordChart.exists_chart | exact GlobalTheory.ZM.CoordChart.exists_chart | (intros; apply GlobalTheory.ZM.CoordChart.exists_chart <;> assumption)
