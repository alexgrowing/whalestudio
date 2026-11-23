import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMulEsymmRootsPow
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_mul_esymm_roots_pow' : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by
  first | exact @GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow | exact GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow | (intros; apply GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow <;> assumption)
