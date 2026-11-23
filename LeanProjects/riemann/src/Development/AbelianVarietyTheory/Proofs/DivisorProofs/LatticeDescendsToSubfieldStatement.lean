import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDescendsToSubfield
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_descends_to_subfield : ∀ (X : Scheme.{0}) [IsIntegral X] (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) (h n : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)) (g : Fin n → Fin h → U.Bp) (S : Fin n → Fin h → Kbar X), Splits U L g S → (∀ k i, (g k i : Kbar X) ∈ K') → (∀ k i, S k i ∈ K') → IsDescended K' U L := by
  first | exact @GlobalTheory.BplusDescent.isDescended_of_splits | exact GlobalTheory.BplusDescent.isDescended_of_splits | (intros; apply GlobalTheory.BplusDescent.isDescended_of_splits <;> assumption)
