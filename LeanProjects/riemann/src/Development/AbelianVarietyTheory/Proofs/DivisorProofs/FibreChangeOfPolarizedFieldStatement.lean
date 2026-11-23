import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreChangeOfPolarizedField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_change_of_polarized_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k k' : Type) [Field k] [Field k'] (f : k →+* k') (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ (Q : Out.PolAV (Sp k')) (ψ : Q.A.left ⟶ φ.P.A.left), IsPolFibre f φ.P Q ψ → ∃ (φ' : Fib k') (m' : CubeMap φ'.G t.G) (χ : φ'.G.left ⟶ φ.G.left) (ψ' : φ'.P.A.left ⟶ φ.P.A.left), φ'.P = Q ∧ HEq ψ' ψ ∧ FibAt t (spMap f ≫ x) φ' m' ∧ IsGrpPullback φ'.G φ.G (spMap f) χ ∧ χ ≫ m.F = m'.F ∧ φ'.q.left ≫ ψ' = χ ≫ φ.q.left ∧ Module.finrank ℤ φ'.X = Module.finrank ℤ φ.X := by
  first | exact @GlobalTheory.BdFib.exists_fibAt_baseChange | exact GlobalTheory.BdFib.exists_fibAt_baseChange | (intros; apply GlobalTheory.BdFib.exists_fibAt_baseChange <;> assumption)
