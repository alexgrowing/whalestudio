import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormConjugatePoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_conjugate_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (z z' : Sp ℂ ⟶ X), z' = spMap (starRingEnd ℂ) ≫ z → ∀ (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ) (g' : TanM z' t.G →ₗ[ℂ] TanM z' t.G →ₗ⋆[ℂ] ℂ), (∀ (v : TanM z t.G) (v' : TanM z' t.G), (tv v').left = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ (tv v).left → g' v' v' = starRingEnd ℂ (g v v)) → ∀ C : ℝ, AbLe g C → AbLe g' C := by
  first | exact @GlobalTheory.AbLeConj.abLe_conj | exact GlobalTheory.AbLeConj.abLe_conj | (intros; apply GlobalTheory.AbLeConj.abLe_conj <;> assumption)
