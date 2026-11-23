import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianMapCochainFrameIndependence
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_cochain_frame_independence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [CharZero k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ (n : ℕ) (v : Fin n → (epsR k ⟶ φ.P.A)), IsLieBasis v → ∀ q : TanM x t.G →ₗ[k] (Fin n → k), IsAbMap φ m v q → ∀ (r : ℕ) (ε : Fin r → TanM x t.G), IsCochFrame t x ε → Module.finrank ℤ φ.X = r → LinearIndependent k ε ∧ LinearMap.ker q = Submodule.span k (Set.range ε) := by
  first | exact @GlobalTheory.BdFib.ker_eq_span_cochFrame | exact GlobalTheory.BdFib.ker_eq_span_cochFrame | (intros; apply GlobalTheory.BdFib.ker_eq_span_cochFrame <;> assumption)
