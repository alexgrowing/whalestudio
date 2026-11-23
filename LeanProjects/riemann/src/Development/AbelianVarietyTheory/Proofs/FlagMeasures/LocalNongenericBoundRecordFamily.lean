import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetAmplitudeBoundLocalStatement

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem local_nongeneric_bound_record_family :
    ∀ (C : ℝ), 39 ≤ C → (∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C) ∧
      (∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C ∧ Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBoundOfLargeRank D C ∧ Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C) ∧
      ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C ∧ Formalism.MainNotions.UniformConstantsAndStatements.admF5 Fm C := by
  intro C hC
  have h1 : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C := by
    intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP
    exact GlobalTheory.T.hermitianDoubleCoset_amplitude_bound_local C hC M hM H r k P hk hV hP
  have h2 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C := fun D hk => h1 _ _ hk
  have h3 : ∀ D : D7, Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C := fun D => h2 D
  exact ⟨h1, fun D => ⟨h2 D, h2 D, h3 D⟩, fun Fm => ⟨fun x i => h2 _, fun x i => h3 _⟩⟩

end GlobalTheory
