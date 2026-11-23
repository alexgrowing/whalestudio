import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZeros
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_parameters_partition_extended_by_zeros : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), (k : ℕ) + 1 = D.R.m → n = D.R.r + k * D.R.t → N = n + D.R.t → IsEnum (parB (Ptw D) k τ) lam ε → IsEnum (parB (Ptw D) D.R.m τ) lam' ε' → ε = allPos n ∧ ε' = allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = expS D k τ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + expT D k τ) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (allPos n) lam a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (allPos N) lam' b = -(x₁ : ℝ) - ν (Fin.rev b) := by
  first | exact @GlobalTheory.LastStepParam.lastStep_param | exact GlobalTheory.LastStepParam.lastStep_param | (intros; apply GlobalTheory.LastStepParam.lastStep_param <;> assumption)
