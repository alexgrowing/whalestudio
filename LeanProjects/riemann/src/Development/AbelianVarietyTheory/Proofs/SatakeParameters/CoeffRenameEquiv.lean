import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ShapeDegreeParity
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TeichmullerFactorisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

namespace GlobalTheory.InertCompare

section Series

variable {l : ℕ} [Fact l.Prime]

variable {d : ℕ} [NeZero d]

def twoCopies (d : ℕ) : ZMod d × Bool ≃ ZMod d ⊕ ZMod d where
  toFun x := if x.2 then Sum.inr x.1 else Sum.inl x.1
  invFun := Sum.elim (fun s => (s, false)) (fun s => (s, true))
  left_inv := by rintro ⟨s, _ | _⟩ <;> rfl
  right_inv := by rintro (s | s) <;> rfl

end Series

section Product

variable (D : D7) (l : ℕ) [Fact l.Prime]

end Product

end GlobalTheory.InertCompare
