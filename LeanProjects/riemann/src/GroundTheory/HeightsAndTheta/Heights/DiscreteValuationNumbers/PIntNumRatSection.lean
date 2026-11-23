import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open GroundTheory.Heights₂.Heights.FieldNumbers

universe u

theorem relDim_eq_of_ringKrullDim {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} (I : Ideal (MRing ι F)) (n : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    relDim I = (n : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  show ((((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) = _
  push_cast
  simp
  rfl

theorem IntNumRatSection.proof (h : CutRational.Statement.{u}) : IntNumRatSection.Statement.{u} := by
  intro F _ K _ _ ι _ n V hV hdim L A f g α β hf hg hfV hgV hA
  have hrel : relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    relDim_eq_of_ringKrullDim V (n + 1) hdim
  have hAeq : (fun k => (α k : ℤ) - β k) = A := funext hA
  have := h F K ι V hV n hrel α β f g hf hg hfV hgV L
  rw [hAeq] at this
  exact this

end GroundTheory.Heights₂.Heights.NumbersDVR
