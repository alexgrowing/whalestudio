import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMorphismOfStalkMaps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_of_stalk_maps : ∀ (B T S : Scheme.{0}) (t : T ⟶ B) (s : S ⟶ B) (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → (∀ x, h x ≫ s = T.fromSpecStalk x ≫ t) → (∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ) → ∃ g : T ⟶ S, ∀ x, T.fromSpecStalk x ≫ g = h x := by
  first | exact @GlobalTheory.GlueStalk.exists_glue_of_stalks | exact GlobalTheory.GlueStalk.exists_glue_of_stalks | (intros; apply GlobalTheory.GlueStalk.exists_glue_of_stalks <;> assumption)
