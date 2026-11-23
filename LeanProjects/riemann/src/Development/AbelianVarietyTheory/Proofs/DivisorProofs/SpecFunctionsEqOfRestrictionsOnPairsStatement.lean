import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFunctionsEqOfRestrictionsOnPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs : ∀ {X : Scheme.{0}} (B B' : Type) [CommRing B] [CommRing B'] (x : Sp B ⟶ X) (ψ : Sp B' ⟶ Sp B) (a b : B'), (∀ (V' : (Sp B').affineOpens) (p : Pair x), V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 → (secMap (𝟙 (Sp B')) V'.1).hom a = (secMap (𝟙 (Sp B')) V'.1).hom b) → a = b := by
  first | exact @GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | exact GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | (intros; apply GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs <;> assumption)
