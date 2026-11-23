import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActSpreadFromDenseFibresAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oAct_spread_from_dense_fibres_abelianScheme : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] (act₀ : J → (A ⟶ A)), Subring.closure (Set.range a) = ⊤ → IsAbelianScheme A → (∀ j, IsMonHom (act₀ j)) → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (φ : G.left ⟶ A.left) (act : OAct O G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ ∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left} → ∃ r : OAct O A, (∀ j, r.act (a j) = act₀ j) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  first | exact @GlobalTheory.oAct_spread_of_dense_fibres | exact GlobalTheory.oAct_spread_of_dense_fibres | (intros; apply GlobalTheory.oAct_spread_of_dense_fibres <;> assumption)
