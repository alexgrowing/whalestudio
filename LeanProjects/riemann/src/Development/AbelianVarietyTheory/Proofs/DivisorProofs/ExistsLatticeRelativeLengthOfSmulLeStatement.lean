import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLe
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeRelativeLength_of_smul_le : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X' X : Submodule (Int0 v) M), X' ≤ X → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ c : Int0 v, c ≠ 0 → (∀ x ∈ X, c • x ∈ X') → ∃ r : ℝ, RelLen v X' X r := by
  first | exact @GlobalTheory.SubLen.exists_relLen_of_smul_le | exact GlobalTheory.SubLen.exists_relLen_of_smul_le | (intros; apply GlobalTheory.SubLen.exists_relLen_of_smul_le <;> assumption)
