import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionOpenLocus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_open_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (f : Y ⟶ X), IsProper p → ∀ (k : Type) [Field k] (g : Sp k ⟶ Y) (T : TorusExtension ((Over.pullback (g ≫ f)).obj t.G)), ∃ U : Y.Opens, g (IsLocalRing.closedPoint k) ∈ U ∧ ∀ y : Sp Qb ⟶ Y, y (IsLocalRing.closedPoint Qb) ∈ U → g (IsLocalRing.closedPoint k) ⤳ y (IsLocalRing.closedPoint Qb) → TorRk t (y ≫ f) (@Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _) := by
  first | exact @GlobalTheory.BdFib.GenRk.exists_open_torRk_of_specializes | exact GlobalTheory.BdFib.GenRk.exists_open_torRk_of_specializes | (intros; apply GlobalTheory.BdFib.GenRk.exists_open_torRk_of_specializes <;> assumption)
