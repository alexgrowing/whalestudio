import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDegree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lie_eigen_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I → (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∀ (V : Type) [AddCommGroup V] [Module K V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G z V) (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r → ∃ (d : ℕ) (D : ConjData C p (𝓞 E) d) (e : V ≃ₗ[K] (Fin d → K)), (∀ i v, v ∈ Y.lieLat M i ↔ e v ∈ D.lie i) ∧ ∀ a v, e (r a v) = (D.ρ a).mulVec (e v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.TopH2.lieLat_conjData | exact GlobalTheory.CompanionTheory.Ar.Conj.TopH2.lieLat_conjData | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.TopH2.lieLat_conjData <;> assumption)
