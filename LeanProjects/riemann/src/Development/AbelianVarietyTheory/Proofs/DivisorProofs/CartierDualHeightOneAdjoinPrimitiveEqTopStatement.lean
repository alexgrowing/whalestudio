import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) → Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} = ⊤ := by
  first | exact @GlobalTheory.HeightOneDual.adjoin_primitive_eq_top | exact GlobalTheory.HeightOneDual.adjoin_primitive_eq_top | (intros; apply GlobalTheory.HeightOneDual.adjoin_primitive_eq_top <;> assumption)
