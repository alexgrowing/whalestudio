import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverTorusSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cover_torus_split : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (f : Y ⟶ X), IsProper p → ∀ y₀ : Y, ∃ (W : Scheme.{0}) (_ : IsIntegral W) (π : W ⟶ Y) (r : ℕ) (u : splitTorus W (Fin r → ℤ) ⟶ (Over.pullback (π ≫ f)).obj t.G), IsFinite π ∧ IsLocallyNoetherian W ∧ π (genericPoint W) = y₀ ∧ IsMonHom u ∧ (∀ (k : Type) [Field k] (g : Sp k ⟶ W), g (IsLocalRing.closedPoint k) = genericPoint W → IsClosedImmersion ((Over.pullback g).map u).left) ∧ ∃ (k : Type) (_ : Field k) (g : Sp k ⟶ Y) (T : TorusExtension ((Over.pullback (g ≫ f)).obj t.G)), g (IsLocalRing.closedPoint k) = y₀ ∧ @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ = r := by
  first | exact @GlobalTheory.BdFib.exists_splitTorus_hom_normal_cover | exact GlobalTheory.BdFib.exists_splitTorus_hom_normal_cover | (intros; apply GlobalTheory.BdFib.exists_splitTorus_hom_normal_cover <;> assumption)
