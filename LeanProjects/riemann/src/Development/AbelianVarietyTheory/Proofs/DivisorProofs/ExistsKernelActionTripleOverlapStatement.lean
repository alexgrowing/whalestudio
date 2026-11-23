import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelActionTripleOverlap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelAction_triple_overlap : ∀ (S : Scheme.{0}) (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A) (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsCharacter χ → ∃ (W : Scheme.{0}) (m₁₂ m₂₃ m₁₃ : W ⟶ (A ⊗ (N ⊗ T)).left), IsPullback m₁₂ m₂₃ (actMap i T).left (prMap A N T).left ∧ m₁₃ ≫ (prMap A N T).left = m₁₂ ≫ (prMap A N T).left ∧ m₁₃ ≫ (actMap i T).left = m₂₃ ≫ (actMap i T).left ∧ pullTop m₁₃ (pullTop (snd A (N ⊗ T)).left χ) = pullTop m₁₂ (pullTop (snd A (N ⊗ T)).left χ) * pullTop m₂₃ (pullTop (snd A (N ⊗ T)).left χ) := by
  first | exact @GlobalTheory.CharKer.triOverlap | exact GlobalTheory.CharKer.triOverlap | (intros; apply GlobalTheory.CharKer.triOverlap <;> assumption)
