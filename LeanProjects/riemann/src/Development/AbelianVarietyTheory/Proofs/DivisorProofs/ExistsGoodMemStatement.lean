import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_good_of_closedImmersions : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] (x : Y₀), ∃ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, x ∈ U := by
  first | exact @GlobalTheory.FerrandPush.exists_good_mem | exact GlobalTheory.FerrandPush.exists_good_mem | (intros; apply GlobalTheory.FerrandPush.exists_good_mem <;> assumption)
