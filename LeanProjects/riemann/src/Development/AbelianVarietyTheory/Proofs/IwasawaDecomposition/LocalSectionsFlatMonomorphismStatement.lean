import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSectionsFlatMonomorphism
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_of_local_maps_agree_at_generic_points : ∀ (S T U Y : Scheme.{0}) (t : T ⟶ S) (s : Y ⟶ S) (j : U ⟶ T) (g : U ⟶ Y), LocallyOfFiniteType s → IsSeparated s → S.IsSeparated → IsLocallyNoetherian T → IsNormalScheme T → IsReduced U → IsLocallyNoetherian U → Mono j → Flat j → g ≫ s = j ≫ t → (∀ x : T, ∃ (V : T.Opens) (hx : x ∈ V) (h : V.toScheme ⟶ Y) (p : T) (hp : p ∈ V) (v : Spec (T.presheaf.stalk p) ⟶ U), p ⤳ x ∧ (∀ q : T, q ⤳ p → q = p) ∧ v ≫ j = T.fromSpecStalk p ∧ V.fromSpecStalkOfMem p hp ≫ h = v ≫ g) → ∃ F : T ⟶ Y, F ≫ s = t ∧ j ≫ F = g := by
  first | exact @GlobalTheory.GlueDense.exists_glue_of_flat_dense | exact GlobalTheory.GlueDense.exists_glue_of_flat_dense | (intros; apply GlobalTheory.GlueDense.exists_glue_of_flat_dense <;> assumption)
