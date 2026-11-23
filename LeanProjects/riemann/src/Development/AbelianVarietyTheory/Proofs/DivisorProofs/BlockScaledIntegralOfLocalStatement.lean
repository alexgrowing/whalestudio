import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_scaled_integral_of_local : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ)
    (t : Fin q → ℝ) (m : ℕ) (ξ : κ → F) (j : κ),
    (∀ v : Pl F, evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) ∈ v.adicCompletionIntegers F) →
    IsIntegral ℤ ((m : F) * ξ j) := by
  first | exact @GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem | exact GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem | (intros; apply GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem <;> assumption)
