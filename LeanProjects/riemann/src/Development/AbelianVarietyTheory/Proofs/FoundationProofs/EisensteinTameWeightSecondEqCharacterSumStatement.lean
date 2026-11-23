import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinTameWeightSecondEqCharacterSum
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters : ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ, tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  first | exact @GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | exact GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | (intros; apply GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum <;> assumption)
