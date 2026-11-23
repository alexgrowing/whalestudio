import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegPB_of_finite_etale_surjective_cover : ∀ (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0}) (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁) (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y), 3 ≤ n → Odd n → u.Principal → IsFinite p → Etale p → Surjective p → SiegPB c₁ c p → SiegPB c₁ u (p ≫ f) → SiegPB c u f := by
  first | exact @GlobalTheory.siegPB_of_finite_etale_cover | exact GlobalTheory.siegPB_of_finite_etale_cover | (intros; apply GlobalTheory.siegPB_of_finite_etale_cover <;> assumption)
