import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSpreadsOut
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_spreads_out : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S : Scheme.{0}) (f : S ⟶ X) (k : Type) [Field k] (x : Sp k ⟶ S) (T : TorusExtension ((Over.pullback (x ≫ f)).obj t.G)), ∃ (V : Scheme.{0}) (π : V ⟶ S) (v : Sp k ⟶ V), v ≫ π = x ∧ LocallyOfFiniteType π ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ V), ∃ T' : TorusExtension ((Over.pullback (w ≫ π ≫ f)).obj t.G), @Module.finrank ℤ T'.X _ T'.addCommGroup.toAddCommMonoid _ = @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ := by
  first | exact @GlobalTheory.TorusSpread.exists_spread | exact GlobalTheory.TorusSpread.exists_spread | (intros; apply GlobalTheory.TorusSpread.exists_spread <;> assumption)
