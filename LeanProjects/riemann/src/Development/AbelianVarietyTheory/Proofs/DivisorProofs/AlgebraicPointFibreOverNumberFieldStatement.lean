import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointFibreOverNumberField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_point_fibre_over_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (y : Sp Qb ⟶ gen T.Z), y (IsLocalRing.closedPoint Qb) ∈ genBd T.Z → ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb) (y₀ : Sp K₀ ⟶ gen T.Z) (φ : Fib K₀) (m : CubeMap φ.G T.Z.t.G), spMap io₀ ≫ y₀ = y ∧ FibAt T.Z.t (y₀ ≫ genι T.Z) φ m := by
  first | exact @GlobalTheory.BdFibPoint.exists_fibre_at_boundary | exact GlobalTheory.BdFibPoint.exists_fibre_at_boundary | (intros; apply GlobalTheory.BdFibPoint.exists_fibre_at_boundary <;> assumption)
