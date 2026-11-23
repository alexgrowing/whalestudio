import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointDefinedOverNumberField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_point_defined_over_number_field : ∀ (F : Type) [Field F] [NumberField F] (W : Scheme.{0}) (p : W ⟶ Sp F), LocallyOfFiniteType p → ∀ w : Sp Qb ⟶ W, ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb) (w₀ : Sp K₀ ⟶ W), spMap io₀ ≫ w₀ = w := by
  first | exact @GlobalTheory.AlgPt.exists_numberField_point | exact GlobalTheory.AlgPt.exists_numberField_point | (intros; apply GlobalTheory.AlgPt.exists_numberField_point <;> assumption)
