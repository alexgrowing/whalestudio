import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairs
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestType_not_jointShape_smaller_pairs : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → ∀ μ', ¬ JointShape _ _ (al.length + de.length + t - i) (ga.length + be.length - i) (blattner (lamA al be ga de)) μ') ∧ (i ≤ al.length + de.length → i ≤ ga.length + be.length + t → ∀ μ', ¬ JointShape _ _ (al.length + de.length - i) (ga.length + be.length + t - i) (blattner (lamA al be ga de)) μ') ∧ ((¬ (∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lamA al be ga de a = -(((t : ℚ) + 1) / 2))) → i ≤ al.length + be.length → i ≤ ga.length + de.length → (∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamA' t al be ga de))) ∧ ∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamM' t al be ga de))) := by
  first | exact @GlobalTheory.LowestTypeDrop.lowestType_not_jointShape | exact GlobalTheory.LowestTypeDrop.lowestType_not_jointShape | (intros; apply GlobalTheory.LowestTypeDrop.lowestType_not_jointShape <;> assumption)
