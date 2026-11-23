import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekind
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_generic_isogenous_dedekind : Out.Laws → Out.Laws2 → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (B : Over (Sp R)) [GrpObj B] (Ψ : P.A ⟶ B) (M : LB B.left) (B₀ : Over (Sp K)) [GrpObj B₀] (φ : B₀.left ⟶ B.left) (M₀ : LB B₀.left), IsAbelianScheme B → M.IsLB → M₀.IsLB → IsFinite Ψ.left → Flat Ψ.left → Surjective Ψ.left → IsGrpPullback B₀ B (spMap (algebraMap R K)) φ → LBIso M₀ (M.pull φ) → Out.RelAmple B₀ M₀ → Out.RelAmple B M := by
  first | exact @GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous | exact GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous | (intros; apply GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous <;> assumption)
