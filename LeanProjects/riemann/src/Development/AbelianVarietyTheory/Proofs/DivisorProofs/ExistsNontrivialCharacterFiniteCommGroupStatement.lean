import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_character_finite_comm_group : ∀ (K : Type) [Field K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → (𝟙 N ≠ (1 : N ⟶ N)) → ∃ (T : Over (Sp K)) (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsCharacter χ ∧ χ ≠ 1 := by
  first | exact @GlobalTheory.CharExists.exists_character_ne_one | exact GlobalTheory.CharExists.exists_character_ne_one | (intros; apply GlobalTheory.CharExists.exists_character_ne_one <;> assumption)
