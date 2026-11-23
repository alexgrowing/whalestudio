import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicOpenSectionScaled
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basic_open_section_scaled : ∀ (X : Scheme.{0}) [IsIntegral X] (U V : AffOp X) (a : Γ(X, U.1)), V.1 = X.basicOpen a → ∀ x : V.Bp, ∃ (N : ℕ) (r : U.Bp), (r : Kbar X) = algebraMap Γ(X, U.1) (Kbar X) a ^ N * x := by
  first | exact @GlobalTheory.BplusDescent.exists_pow_mul_mem_of_eq_basicOpen | exact GlobalTheory.BplusDescent.exists_pow_mul_mem_of_eq_basicOpen | (intros; apply GlobalTheory.BplusDescent.exists_pow_mul_mem_of_eq_basicOpen <;> assumption)
