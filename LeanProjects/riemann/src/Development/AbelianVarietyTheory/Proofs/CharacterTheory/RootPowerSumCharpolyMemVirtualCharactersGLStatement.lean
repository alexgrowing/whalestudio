import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGL
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, (fun x : GL (Fin n) F => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F))) ∈ Virt ℂ ℂ (GL (Fin n) F) := by
  first | exact @GlobalTheory.CuspGL.rootSum_charpoly_mem_virt | exact GlobalTheory.CuspGL.rootSum_charpoly_mem_virt | (intros; apply GlobalTheory.CuspGL.rootSum_charpoly_mem_virt <;> assumption)
