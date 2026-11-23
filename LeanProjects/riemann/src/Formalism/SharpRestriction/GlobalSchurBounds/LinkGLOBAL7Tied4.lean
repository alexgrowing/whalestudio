import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColStd
import Formalism.LocalToGlobal.HermitianForms.BothSym

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

def tCVTies {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Nonempty (Formalism.L2.Forms.ColsTiedSym (Fm.D x i)) ∧ flipTwoThree.adm3 (Fm.D x i)

def ColumnValuationFromTwistCompatibility : Prop :=
  ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → flipTwoThree.adm3 D → ∀ u : D.what₂.Word, Nonempty (flipTwoThree.ColVal D u)

theorem tCV_of_tied {eps : ℝ} (Fm : FamP eps) (hCV : ColumnValuationFromTwistCompatibility) (hT : tCVTies Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) := by
  unfold tCVTies at hT
  obtain ⟨x0, hx⟩ := hT
  refine ⟨x0, fun x hx0 i u => ?_⟩
  obtain ⟨⟨t⟩, ha⟩ := hx x hx0 i
  exact hCV _ t ha u

end Formalism.MainNotions.RT
