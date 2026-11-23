import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_lowered_level : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (C : SiegPre h N ζ' s'), N ≠ 0 → IsUnit (N : B') → n ∣ N → j ζ = ζ' ^ (N / n) → ∃ c : SiegPre h n ζ (s' ≫ spMap j), SRel C c (N / n) 1 (𝟙 S) ∧ SRel c C 1 (N / n) (𝟙 S) := by
  first | exact @GlobalTheory.SiegLower.exists_lower | exact GlobalTheory.SiegLower.exists_lower | (intros; apply GlobalTheory.SiegLower.exists_lower <;> assumption)
