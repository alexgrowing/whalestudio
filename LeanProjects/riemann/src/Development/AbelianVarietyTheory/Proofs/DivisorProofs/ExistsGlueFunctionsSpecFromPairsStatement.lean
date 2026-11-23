import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsSpecFromPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_functions_spec_from_pairs : ∀ {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X) (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1)), (∀ p q : Pair x, ∀ hpq : p ≤ q, ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) → ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by
  first | exact @GlobalTheory.CechDR.AffLoc.exists_glue_pair | exact GlobalTheory.CechDR.AffLoc.exists_glue_pair | (intros; apply GlobalTheory.CechDR.AffLoc.exists_glue_pair <;> assumption)
