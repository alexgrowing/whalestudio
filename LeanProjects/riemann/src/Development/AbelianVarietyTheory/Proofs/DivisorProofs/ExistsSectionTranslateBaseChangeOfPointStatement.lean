import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_translate_baseChange_of_point : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R') (G : Over (Sp R)) [GrpObj G] (c : Sp R' ⟶ G.left), c ≫ G.hom = spMap ρ → ∃ (a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G) (Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left), IsPullback Φ (pullback.snd G.hom (spMap ρ)) (snd G G).left c ∧ Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * snd G G).left ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * (snd G G)⁻¹).left := by
  first | exact @GlobalTheory.TransBaseChange.exists_section_translate | exact GlobalTheory.TransBaseChange.exists_section_translate | (intros; apply GlobalTheory.TransBaseChange.exists_section_translate <;> assumption)
