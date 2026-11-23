import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteGroupSchemeSumExtension
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_scheme_sum_extension : ∀ {X : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (xl : Sp K ⟶ X) (A : FG M (Sp K)), (∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')), (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J → e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised <;> assumption)
