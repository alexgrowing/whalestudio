import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_object_odd_level_rigid : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  first | exact @GlobalTheory.SiegRigid.eq_of_sRelBy | exact GlobalTheory.SiegRigid.eq_of_sRelBy | (intros; apply GlobalTheory.SiegRigid.eq_of_sRelBy <;> assumption)
