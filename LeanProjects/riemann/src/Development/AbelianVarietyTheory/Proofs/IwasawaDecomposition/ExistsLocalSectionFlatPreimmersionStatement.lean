import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionFlatPreimmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_section_flat_preimmersion : ∀ (S T U Y : Scheme.{0}) (t : T ⟶ S) (s : Y ⟶ S) (j : U ⟶ T) (g : U ⟶ Y), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → IsNormalScheme T → IsReduced U → IsPreimmersion j → Flat j → g ≫ s = j ≫ t → ∀ p : T, p ∈ Set.range j → (∀ q : T, q ⤳ p → q = p) → ∃ (W : T.Opens) (f : W.toScheme ⟶ Y) (v : Spec (T.presheaf.stalk p) ⟶ U), p ∈ W ∧ v ≫ j = T.fromSpecStalk p ∧ f ≫ s = W.ι ≫ t ∧ ∀ (T' : Scheme.{0}) (u : T' ⟶ W.toScheme) (w : T' ⟶ U), u ≫ W.ι = w ≫ j → u ≫ f = w ≫ g := by
  first | exact @GlobalTheory.SpreadFromGeneric.exists_spread | exact GlobalTheory.SpreadFromGeneric.exists_spread | (intros; apply GlobalTheory.SpreadFromGeneric.exists_spread <;> assumption)
