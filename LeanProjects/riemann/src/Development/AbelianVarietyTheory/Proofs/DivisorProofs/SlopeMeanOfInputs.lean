import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantDivisorBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WallSmallnessOfDegreesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WallBoundOfPolySizeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeOfAntisymmetricFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeChangeOfRelabellingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeFinalOfShapeChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyChangeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAsymptoticExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundFromExactAsymptotic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualVolumeAndSlopeMeanStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem vol_pos_assembly {D : D7} {Y : ShimX D.what₂.Tau} {A : SlopeTestRemainingChoices Y} (h : Degrees A) : 0 < Y.vol := by
  obtain ⟨hw, hv, -⟩ := h
  have hc : Fintype.card Y.Comp ≠ 0 := Fintype.card_ne_zero
  have hne : Nonempty Y.Comp := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hc)
  rw [hv]
  exact Finset.sum_pos (fun c _ => hw c) Finset.univ_nonempty

end GlobalTheory.Mean4
