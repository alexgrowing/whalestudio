import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
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
theorem _root_.GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (d : ℕ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → ∃ (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec), (Nonempty σ → IsProjOver s) ∧ ProjRep I s M th ∧ (I.FG → LocallyOfFinitePresentation s) ∧ ((∀ e ≥ d, Module.Flat R (↥(MvPolynomial.homogeneousSubmodule σ R e) ⧸ (I.restrictScalars R).comap (MvPolynomial.homogeneousSubmodule σ R e).subtype)) → Flat s) := by
  first | exact @GlobalTheory.ProjFlat.exists_projRep_flat | exact GlobalTheory.ProjFlat.exists_projRep_flat | (intros; apply GlobalTheory.ProjFlat.exists_projRep_flat <;> assumption)
