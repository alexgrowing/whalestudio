import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionsFlatBaseChangeBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFunctions_flatBaseChange_bijective : ∀ {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'], Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  first | exact @GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective | exact GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective | (intros; apply GlobalTheory.PDiv.liftSemi_prim_baseChange_bijective <;> assumption)
