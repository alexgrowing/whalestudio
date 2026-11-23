import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions

theorem Link3F_of_Link3 (h : Link3) : Link3F := fun _ Fm x i => h (Fm.D x i)

theorem Link1F_of_count
    (h : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
      Transference → ∃ C₀ : ℝ, 2 ≤ C₀ ∧ Formalism.MainNotions.flipTwoThree.MsCountF Fm C₀) : Link1F := by
  intro eps Fm hH hT
  obtain ⟨C₀, hC, hM⟩ := h eps Fm hH hT
  exact Formalism.MainNotions.flipTwoThree.familyMass_of_massCount Fm C₀ hC hM

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality
