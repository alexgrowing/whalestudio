import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPoint
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusExtension_points_pullback_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  first | exact @GlobalTheory.AlphaPair.exists_isTorExt_pull | exact GlobalTheory.AlphaPair.exists_isTorExt_pull | (intros; apply GlobalTheory.AlphaPair.exists_isTorExt_pull <;> assumption)
