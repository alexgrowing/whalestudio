import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_iso_of_projectiveCoordinateRepresentation : ∀ (R σ : Type) [CommRing R] (I I' : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R) (M : LB Z) (M' : LB Z') (th : σ → M.Sec) (th' : σ → M'.Sec), ProjRep I s M th → ProjRep I' s' M' th' → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ → ((∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ↔ ∀ F ∈ I', MvPolynomial.eval₂ β v F = 0)) → ∃ e : Z ≅ Z', e.hom ≫ s' = s ∧ LBIso M (M'.pull e.hom) ∧ ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Z) (v : σ → R'), SecCoord M th x v ↔ SecCoord M' th' (x ≫ e.hom) v := by
  first | exact @GlobalTheory.RepUniq.exists_iso_of_projRep | exact GlobalTheory.RepUniq.exists_iso_of_projRep | (intros; apply GlobalTheory.RepUniq.exists_iso_of_projRep <;> assumption)
