import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classified_of_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegZar.classified_of_local | exact GlobalTheory.SiegZar.classified_of_local | (intros; apply GlobalTheory.SiegZar.classified_of_local <;> assumption)
