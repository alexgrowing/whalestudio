import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.Finite K G.omega ∧ Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧ Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  first | exact @GlobalTheory.PDivGroup.finrank_rigExt_omega | exact GlobalTheory.PDivGroup.finrank_rigExt_omega | (intros; apply GlobalTheory.PDivGroup.finrank_rigExt_omega <;> assumption)
