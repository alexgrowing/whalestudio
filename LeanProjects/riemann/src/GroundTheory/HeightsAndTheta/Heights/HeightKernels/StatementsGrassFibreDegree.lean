import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

def GrassFibreDegree.Statement : Prop :=
  ∀ (n p : ℕ), p.Prime →
    vertR (grassIdeal 1 1 n) (fun _ : Fin n => fsMulti (plBlocks 1 1 n)) (C (p : ℤ)) = Real.log p

example : PLift (Nat.Prime 2) × Ideal (MRing (plBlocks 1 1 2)) × HermLine (plBlocks 1 1 2) :=
  ⟨⟨Nat.prime_two⟩, grassIdeal 1 1 2, fsMulti (plBlocks 1 1 2)⟩

end

end GroundTheory.Heights₂.Heights
