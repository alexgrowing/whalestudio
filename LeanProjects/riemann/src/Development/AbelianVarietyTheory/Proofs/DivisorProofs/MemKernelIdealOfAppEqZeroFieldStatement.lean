import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelIdealOfAppEqZeroField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G → g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  first | exact @GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | exact GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | (intros; apply GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero <;> assumption)
