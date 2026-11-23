import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModPSquaredStalkSurjective
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.mod_p_squared_stalk_surjective : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ y : X, Function.Surjective (π.stalkMap y).hom ∧ ∀ z, (π.stalkMap y).hom z = 0 ↔ ∃ w, z = p * w := by
  first | exact @_root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker | exact _root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker | (intros; apply _root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker <;> assumption)
