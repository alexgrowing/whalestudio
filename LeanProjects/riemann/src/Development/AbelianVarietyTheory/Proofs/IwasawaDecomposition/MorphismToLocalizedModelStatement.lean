import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MorphismToLocalizedModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_to_localized_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → ∀ F : pullback Z.s (spMap b) ⟶ C.X, F ≫ C.s = pullback.snd _ _ → (∀ u : Xo.XF c ⟶ pullback Z.s (spMap b), u ≫ pullback.fst _ _ = Z.j → u ≫ F = C.j) → Dominates Z C b := by
  first | exact @GlobalTheory.TorRef.dominates_of_map_on_part | exact GlobalTheory.TorRef.dominates_of_map_on_part | (intros; apply GlobalTheory.TorRef.dominates_of_map_on_part <;> assumption)
