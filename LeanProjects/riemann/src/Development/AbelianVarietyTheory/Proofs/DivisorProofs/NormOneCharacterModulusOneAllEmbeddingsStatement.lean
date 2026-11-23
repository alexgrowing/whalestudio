import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneCharacterModulusOneAllEmbeddings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneCharacter_modulusOne_all_embeddings : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → StandardLatticesGL3.Mod1All (χ 𝔞) := by
  first | exact @GlobalTheory.CharModOne.mod1All_of_isChi | exact GlobalTheory.CharModOne.mod1All_of_isChi | (intros; apply GlobalTheory.CharModOne.mod1All_of_isChi <;> assumption)
