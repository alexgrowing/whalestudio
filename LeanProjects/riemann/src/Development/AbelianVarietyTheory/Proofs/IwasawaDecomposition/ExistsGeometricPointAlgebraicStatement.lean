import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricPointAlgebraic
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_point_algebraic : ∀ {A : Type} [CommRing A] {B : Scheme.{0}} (f : Sp A ⟶ B) [LocallyOfFiniteType f] (x : Sp A) (K' : Type) [Field K']
    [IsAlgClosed K'] (ι : B.residueField (f x) →+* K'),
    ∃ ψ₁ : A →+* K', spMap ψ₁ ≫ f = spMap ι ≫ B.fromSpecResidueField (f x) ∧
      ∀ r, @IsAlgebraic (B.residueField (f x)) K' _ _ ι.toAlgebra (ψ₁ r) := by
  first | exact @GlobalTheory.exists_algebraic_point_of_fiber | exact GlobalTheory.exists_algebraic_point_of_fiber | (intros; apply GlobalTheory.exists_algebraic_point_of_fiber <;> assumption)
